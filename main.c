/*
 * Copyright (c) 2015, NVIDIA CORPORATION.  All rights reserved.
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License, version 2.1, as published by the Free Software Foundation.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/>.
 */

/*
    hevc_parser: a simple HEVC player using VDPAU and Gstreamer
    José Hiram Soltren, <jsoltren@nvidia.com>

    Implements a simple stream parser in accordance with:
    Rec. ITU-T H.265 (04/2013)
    Annex B, Byte stream format.

    Also serves as a basic example of how to use the VDPAU API to play
    H.265/HEVC elemntary streams. Only elementary streams are supported.

    Attempts to play a bit stream using VDPAU. Frames are presented in decode,
    not display, order.

    Depends on a hacked version of gstreamer in order to get SliceHeaderBits
    counts.

    TODO - Implement display order presentation.
    TODO - Upstream bit counting code to gstreamer project.
    TODO - Define window size at run time.
 */

#include <inttypes.h>
#include <unistd.h>
#include <sys/time.h>
#include <vdpau/vdpau_x11.h>
#include "win_x11.h"
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include "gsth265parser.h"

#define MAX_WIN_WIDTH  1920
#define MAX_WIN_HEIGHT 1200

#define NALU_BUFFER_LENGTH 4194304
#define MAX_LUMA_PS 8912896
#define SQRT_MAX_LUMA_PS_X8 8444
#define MAX_DPB_PIC_BUF 6

#define MAX_FRAMES 25

#define HEVC_MAX_REFERENCES 16

#define NUM_OUTPUT_SURFACES 8

#define ARSIZE(x) (sizeof(x) / sizeof((x)[0]))

#define CHECK_STATE \
    if (vdp_st != VDP_STATUS_OK) { \
        printf("Error at %s:%d (%d)\n", __FILE__, __LINE__, (int)vdp_st); \
        exit(1); \
    }

#define QUEUED_FOR_DISPLAY 2
#define QUEUED_FOR_REFERENCE 1
#define NOT_QUEUED 0

static int num_win_ids = 1;
static unsigned short vid_width, vid_height;
static VdpDecoder decoder;
static uint32_t serialNumbers[HEVC_MAX_REFERENCES];
static uint8_t inUse[HEVC_MAX_REFERENCES];
static int displayQueue[NUM_OUTPUT_SURFACES];
static VdpOutputSurface outputSurfaces[NUM_OUTPUT_SURFACES];
static VdpVideoMixer videoMixer;
static uint32_t displayFrameNumber = 0;
static VdpRect outRect;
static VdpRect outRectVid;
static VdpTime gtime = 0;

/*
   Local decoder state.

   Video players must use the VdpPictureInfoHEVC.RefPics[] array to store the
   Specification mandated decoded picture buffer (DPB).

   However, for video player reference picture management, that list alone is
   insufficient. Player applications must keep track of additional state per
   picture.

   hevc_decoder_context keeps track of all decoder state that must be
   maintained by a video player, but is not included as part of the
   VdpPictureInfoHEVC structure. In particular, this structure maintains a
   list of scratch frames, which can be used in the DPB.
 */

typedef enum
{
    UNUSED_FOR_REFERENCE          = 0,
    USED_FOR_SHORT_TERM_REFERENCE = 1,
    USED_FOR_LONG_TERM_REFERENCE  = 2,
} dpb_reference_value;

typedef struct _hevc_decoder_context
{
    VdpVideoSurface scratch_frames[HEVC_MAX_REFERENCES];
    uint8_t MaxDpbSize;
    uint8_t NoOutputOfPriorPicsFlag;
    uint8_t NoRaslOutputFlag;
    uint8_t HandleCraAsBlaFlag;
    int32_t prevPicOrderCntLsb;
    int32_t prevPicOrderCntMsb;
    uint8_t IsFirstPicture;
    int32_t NumPocStFoll;
    int32_t NumPocLtFoll;
    int32_t current_slice_pic_order_cnt_lsb;
    int32_t dpb_slice_pic_order_cnt_lsb[HEVC_MAX_REFERENCES];
    uint8_t dpb_reference_values[HEVC_MAX_REFERENCES];
    uint8_t PicOutputFlag[HEVC_MAX_REFERENCES];
    int8_t  dpb_fullness;
    int8_t  RefPicSetStFoll[8];
    int8_t  RefPicSetLtFoll[8];
    int8_t  vdpau_initialized;
} hevc_decoder_context;

static void PrintUsage(void)
{
    printf("Usage:\n");
    printf("vdpau_hw_hevc [options] elementary_stream.265\n");
    printf("  options: \"-f #\"  -- display at framerate #\n");
    printf("                        (default: display at refresh rate)\n");
    printf("             -l      -- loop continuously\n");
    printf("      anything else  -- this usage message\n");
    printf("  (see the source for further undocumented options\n");

    exit(1);
}

static uint32_t min(uint32_t a, uint32_t b)
{
    return a<b?a:b;
}

static inline int check_for_error(GstH265ParserResult result)
{
    if(result != GST_H265_PARSER_OK)
    {
        printf("%s%d\n",
               "Error in gsth265parser: ",
               result);
        return (-10 - result);
    }
}

static int check_eof(FILE *file)
{
    if(feof(file))
    {
        printf("End of file! Location %#0lx\n", ftell(file));
        return -1;
    }

    return 0;
}

static int check_nalu_result(GstH265ParserResult result)
{
    if(result)
    {
        printf("ERROR: gst_h265_parser_identify_nalu: %x ", result);
        switch(result)
        {
        case 0:
            printf("GST_H265_PARSER_OK\n");
            break;
        case 1:
            printf("GST_H265_PARSER_BROKEN_DATA\n");
            break;
        case 2:
            printf("GST_H265_PARSER_BROKEN_LINK\n");
            break;
        case 3:
            printf("GST_H265_PARSER_ERROR\n");
            break;
        case 4:
            printf("GST_H265_PARSER_NO_NAL\n");
            break;
        case 5:
            printf("GST_H265_PARSER_NO_NAL_END\n");
            break;
        default:
            printf("GST_H265_PARSER_UNKNOWN_ERROR\n");
            break;
        }
        return -1;
    }
    else
    {
        printf("Got NAL.\n");
    }
    return 0;
}

static int free_gst_objects(
    GstH265NalUnit** nalu,
    GstH265SliceHdr** slice,
    GstH265VPS** vps,
    GstH265SPS** sps,
    GstH265PPS** pps,
    GstH265SEIMessage** sei)
{
    free(*nalu);
    free(*slice);
    free(*sps);
    free(*vps);
    free(*pps);
    free(*sei);

    return 0;
}

static int allocate_gst_objects(
    GstH265NalUnit** nalu,
    GstH265SliceHdr** slice,
    GstH265VPS** vps,
    GstH265SPS** sps,
    GstH265PPS** pps,
    GstH265SEIMessage** sei)
{
    *slice = calloc(1, sizeof(GstH265SliceHdr));
    if(*slice == NULL) goto failure;
    *vps = calloc(1, sizeof(GstH265VPS));
    if(*vps == NULL) goto failure;
    *sps = calloc(1, sizeof(GstH265SPS));
    if(*sps == NULL) goto failure;
    *pps = calloc(1, sizeof(GstH265PPS));
    if(*pps == NULL) goto failure;
    *sei = calloc(1, sizeof(GstH265SEIMessage));
    if(*sei == NULL) goto failure;
    *nalu = calloc(1, sizeof(GstH265NalUnit));
    if(*nalu == NULL) goto failure;

    return 0;
failure:
    free_gst_objects(nalu, slice, vps, sps, pps, sei);
    return -1;
}

/* The following functions implement a rudimentary H.265/HEVC
   elementary stream parser:

   peek_next_nal_unit
   get_next_nal_unit
 */

/* Report the type of the next NAL unit in the stream.
   Assumes that stream is already positioned at start of a NAL unit.
Returns:
0, if this is a VCL NAL unit with first_slice_segment_in_pic_flag set.
-1, if end of file is found.
1, otherwise.
 */
static int peek_next_nal_unit(FILE* file)
{
    long start_pos;
    uint8_t a, b, c, type, layer_id, temporal_id;
    uint16_t nal_unit_header;

    /* Report on the type of this NAL Unit. */
    /* Skip the first three bytes, should be 0x0 0x0 0x1. */
    fseek(file, 3, SEEK_CUR);
    if(check_eof(file))
    {
        fseek(file, -3, SEEK_CUR);
        return -1;
    }
    /* nal_unit_header begins after start code prefix. */
    start_pos = ftell(file);
    /* Implement nal_unit_header(), 7.3.1.2, here. */
    a = (uint8_t) fgetc(file);
    b = (uint8_t) fgetc(file);
    c = (uint8_t) fgetc(file);
    if(check_eof(file))
    {
        fseek(file, -3, SEEK_CUR);
        return -1;
    }
    nal_unit_header = a<<8 | b;
    type = (nal_unit_header & 0x7e00) >> 9;
    layer_id = (nal_unit_header & 0x1f8 ) >> 3;
    temporal_id = (nal_unit_header & 0x7) - 1;
    printf("NALU at 0x%08lx, type %d, layer id %d, temporal id %d\n",
           start_pos, type, layer_id, temporal_id);
    /* Go back to where we started. */
    fseek(file, -6, SEEK_CUR);
    return (type >= 0 && type < 32) ? c>>7 : 1;
}

/*
   Read through file for next NAL unit.
   Return it in buf.
   Leave file ready for running get_next_nal_unit again.
 */
static int get_next_nal_unit(FILE* file, const void* buf, int* nal_length)
{
    int found = 0;
    long start_pos = 0, end_pos = 0;
    int nals = 0;

    /* Start by finding the offsets of the first NAL unit in this file. */
    while(!(found))
    {
        uint8_t a, b, c;
        a = (uint8_t) fgetc(file);
        b = (uint8_t) fgetc(file);
        c = (uint8_t) fgetc(file);

        if(check_eof(file)) return -1;

        if(a == 0x00 &&
                b == 0x00 &&
                c == 0x01)
        {
            /* Found a start code prefix. */
            start_pos = ftell(file);
            end_pos = 0;
            printf("Found a start code! Location %#0lx\n", start_pos);
            nals++;
            if(nals == MAX_FRAMES) break;
            /* Now find the position of the next start code prefix,
               or the end of the file. */
            for(;;)
            {
                a = (uint8_t) fgetc(file);
                b = (uint8_t) fgetc(file);
                c = (uint8_t) fgetc(file);

                if (a == 0x00 &&
                        b == 0x00 &&
                        c == 0x01)
                {
                    /* Great! Found another start code prefix. */
                    end_pos = ftell(file);
                    printf("Found another start code! Location %#0lx\n",
                           end_pos);
                    found = 1;
                    break;
                }
                else if (check_eof(file))
                {
                    /* Good enough. Found end of file. */
                    end_pos = ftell(file);
                    printf("Found the end of the file! Location %#0lx\n",
                           end_pos);
                    found = 1;
                    break;
                }
                else
                {
                    /* Not a start code prefix. Try again. */
                    fseek(file, -2, SEEK_CUR);
                }
            }
        }
        else
        {
            /* Not a start code prefix. Try again. */
            fseek(file, -  2, SEEK_CUR);
        }
    }

    *nal_length = end_pos-start_pos+4;
    if(*nal_length > NALU_BUFFER_LENGTH)
    {
        printf("Skipping jumbo sized NALU of size %x\n", *nal_length);
        fseek(file, -2, SEEK_CUR);
        return -1;
    }
    /* Have a start and end position. Grab a NAL unit. */
    /* Rewind an additional 3 to grab the start code. */
    fseek(file, start_pos - end_pos - 3, SEEK_CUR);
    /* Make sure to include the trailing end code? */
    /* That's an additional 3 to read for the start. */
    /* API requires a read of one past the end. */

    fread((void *)buf, sizeof(uint8_t), *nal_length, file);

    /* TODO Check for EOF padding */
    if(check_eof(file))
    {
        /* Need to add a start code after the last NAL unit in the file. */
        uint8_t eos[3] = { 0x0, 0x0, 0x1 };
        memcpy((void *)(buf + *nal_length - 1), (const void *)&eos, 3);
        *nal_length = *nal_length + 3;
    }

    if(end_pos > 0)
    {
        /* Put file pointer just before start code for next frame. */
        fseek(file, -4, SEEK_CUR);
    }

    printf("nal_length is %x\n", *nal_length);

    return 0;
}

static int update_picture_info_sps(
    VdpPictureInfoHEVC *pi,
    GstH265SPS *sps)
{
    int i, j;

    pi->pic_width_in_luma_samples =
        sps->pic_width_in_luma_samples;
    pi->pic_height_in_luma_samples =
        sps->pic_height_in_luma_samples;
    pi->log2_min_luma_coding_block_size_minus3 =
        sps->log2_min_luma_coding_block_size_minus3;
    pi->log2_diff_max_min_luma_coding_block_size =
        sps->log2_diff_max_min_luma_coding_block_size;
    pi->log2_min_transform_block_size_minus2 =
        sps->log2_min_transform_block_size_minus2;
    pi->log2_diff_max_min_transform_block_size =
        sps->log2_diff_max_min_transform_block_size;
    pi->pcm_enabled_flag = sps->pcm_enabled_flag;
    if(sps->pcm_enabled_flag)
    {
        pi->log2_min_pcm_luma_coding_block_size_minus3 =
            sps->log2_min_pcm_luma_coding_block_size_minus3;
        pi->log2_diff_max_min_pcm_luma_coding_block_size =
            sps->log2_diff_max_min_pcm_luma_coding_block_size;
        pi->pcm_sample_bit_depth_luma_minus1 =
            sps->pcm_sample_bit_depth_luma_minus1;
        pi->pcm_sample_bit_depth_chroma_minus1 =
            sps->pcm_sample_bit_depth_chroma_minus1;
        pi->pcm_loop_filter_disabled_flag =
            sps->pcm_loop_filter_disabled_flag;
    }
    else
    {
        pi->log2_min_pcm_luma_coding_block_size_minus3 = 0;
        pi->log2_diff_max_min_pcm_luma_coding_block_size = 0;
        pi->pcm_sample_bit_depth_luma_minus1 = 0;
        pi->pcm_sample_bit_depth_chroma_minus1 = 0;
        pi->pcm_loop_filter_disabled_flag = 0;
    }
    pi->bit_depth_luma_minus8 = sps->bit_depth_luma_minus8;
    pi->bit_depth_chroma_minus8 = sps->bit_depth_chroma_minus8;
    pi->strong_intra_smoothing_enabled_flag =
        sps->strong_intra_smoothing_enabled_flag;
    pi->max_transform_hierarchy_depth_intra =
        sps->max_transform_hierarchy_depth_intra;
    pi->max_transform_hierarchy_depth_inter =
        sps->max_transform_hierarchy_depth_inter;
    pi->amp_enabled_flag = sps->amp_enabled_flag;
    pi->separate_colour_plane_flag = sps->separate_colour_plane_flag;
    pi->log2_max_pic_order_cnt_lsb_minus4 =
        sps->log2_max_pic_order_cnt_lsb_minus4;
    pi->num_short_term_ref_pic_sets = sps->num_short_term_ref_pic_sets;
    pi->long_term_ref_pics_present_flag = sps->long_term_ref_pics_present_flag;
    pi->num_long_term_ref_pics_sps = sps->num_long_term_ref_pics_sps;
    pi->sps_temporal_mvp_enabled_flag =
        sps->temporal_mvp_enabled_flag; /* non-compliant name in gstreamer */
    pi->sample_adaptive_offset_enabled_flag =
        sps->sample_adaptive_offset_enabled_flag;
    pi->scaling_list_enabled_flag = sps->scaling_list_enabled_flag;
    pi->chroma_format_idc = sps->chroma_format_idc;
    /* non-compliant name. TODO - is layer zero correct here? */
    pi->sps_max_dec_pic_buffering_minus1 =
        sps->max_dec_pic_buffering_minus1[0];

    /* 
     * SPS Scaling Lists
     *
     * gstreamer takes care of initializing a default scaling list, or
     * patching it if sps->scaling_list_data_present_flag is set.
     */

    for(i=0; i<6; i++)
    {
        for(j=0; j<16; j++)
        {
            pi->ScalingList4x4[i][j] =
                sps->scaling_list.scaling_lists_4x4[i][j];
        }
    }

    for(i=0; i<6; i++)
    {
        for(j=0; j<64; j++)
        {
            pi->ScalingList8x8[i][j] =
                sps->scaling_list.scaling_lists_8x8[i][j];
        }
    }

    for(i=0; i<6; i++)
    {
        for(j=0; j<64; j++)
        {
            pi->ScalingList16x16[i][j] =
                sps->scaling_list.scaling_lists_16x16[i][j];
        }
    }

    for(i=0; i<2; i++)
    {
        for(j=0; j<64; j++)
        {
            pi->ScalingList32x32[i][j] =
                sps->scaling_list.scaling_lists_32x32[i][j];
        }
    }

    for(i=0; i<6; i++)
    {
        pi->ScalingListDCCoeff16x16[i] =
            sps->scaling_list.scaling_list_dc_coef_minus8_16x16[i] + 8;
    }

    for(i=0; i<2; i++)
    {
        pi->ScalingListDCCoeff32x32[i] =
            sps->scaling_list.scaling_list_dc_coef_minus8_32x32[i] + 8;
    }

    return 0;
}

static int update_picture_info_pps(
    VdpPictureInfoHEVC *pi,
    GstH265PPS *pps)
{
    int i, j;

    pi->dependent_slice_segments_enabled_flag =
        pps->dependent_slice_segments_enabled_flag;
    pi->slice_segment_header_extension_present_flag =
        pps->slice_segment_header_extension_present_flag;
    pi->sign_data_hiding_enabled_flag = pps->sign_data_hiding_enabled_flag;
    pi->cu_qp_delta_enabled_flag = pps->cu_qp_delta_enabled_flag;
    pi->diff_cu_qp_delta_depth = pps->diff_cu_qp_delta_depth;
    pi->init_qp_minus26 = pps->init_qp_minus26;
    pi->pps_cb_qp_offset = pps->cb_qp_offset;
    pi->pps_cr_qp_offset = pps->cr_qp_offset;
    pi->constrained_intra_pred_flag = pps->constrained_intra_pred_flag;
    pi->weighted_pred_flag = pps->weighted_pred_flag;
    pi->weighted_bipred_flag = pps->weighted_bipred_flag;
    pi->transform_skip_enabled_flag = pps->transform_skip_enabled_flag;
    pi->transquant_bypass_enabled_flag = pps->transquant_bypass_enabled_flag;
    pi->entropy_coding_sync_enabled_flag =
        pps->entropy_coding_sync_enabled_flag;
    pi->log2_parallel_merge_level_minus2 =
        pps->log2_parallel_merge_level_minus2;
    pi->num_extra_slice_header_bits = pps->num_extra_slice_header_bits;
    pi->loop_filter_across_tiles_enabled_flag =
        pps->loop_filter_across_tiles_enabled_flag;
    pi->pps_loop_filter_across_slices_enabled_flag =
        pps->loop_filter_across_slices_enabled_flag;
    pi->output_flag_present_flag = pps->output_flag_present_flag;
    pi->num_ref_idx_l0_default_active_minus1 =
        pps->num_ref_idx_l0_default_active_minus1;
    pi->num_ref_idx_l1_default_active_minus1 =
        pps->num_ref_idx_l1_default_active_minus1;
    pi->lists_modification_present_flag = pps->lists_modification_present_flag;
    pi->cabac_init_present_flag = pps->cabac_init_present_flag;
    pi->pps_slice_chroma_qp_offsets_present_flag =
        pps->slice_chroma_qp_offsets_present_flag;
    pi->deblocking_filter_control_present_flag =
        pps->deblocking_filter_control_present_flag;
    pi->deblocking_filter_override_enabled_flag =
        pps->deblocking_filter_override_enabled_flag;
    pi->pps_deblocking_filter_disabled_flag =
        pps->deblocking_filter_disabled_flag;
    pi->pps_beta_offset_div2 = pps->beta_offset_div2;
    pi->pps_tc_offset_div2 = pps->tc_offset_div2;
    pi->tiles_enabled_flag = pps->tiles_enabled_flag;
    pi->uniform_spacing_flag = pps->uniform_spacing_flag;
    pi->num_tile_columns_minus1 = pps->num_tile_columns_minus1;
    pi->num_tile_rows_minus1 = pps->num_tile_rows_minus1;

    for(i=0; i<19 /* from gstreamer */; i++)
    {
        pi->column_width_minus1[i] = pps->column_width_minus1[i];
    }
    for(; i<22 /* from VDPAU */; i++)
    {
        pi->column_width_minus1[i] = 0;
    }

    for(i=0; i<20 /* from VDPAU */; i++)
    {
        pi->row_height_minus1[i] = pps->row_height_minus1[i];
    }

    /* 
     * PPS Scaling Lists
     *
     * gstreamer takes care of initializing a default scaling list, or
     * patching it if pps->scaling_list_data_present_flag is set.
     */

    for(i=0; i<6; i++)
    {
        for(j=0; j<16; j++)
        {
            pi->ScalingList4x4[i][j] =
                pps->scaling_list.scaling_lists_4x4[i][j];
        }
    }

    for(i=0; i<6; i++)
    {
        for(j=0; j<64; j++)
        {
            pi->ScalingList8x8[i][j] =
                pps->scaling_list.scaling_lists_8x8[i][j];
        }
    }

    for(i=0; i<6; i++)
    {
        for(j=0; j<64; j++)
        {
            pi->ScalingList16x16[i][j] =
                pps->scaling_list.scaling_lists_16x16[i][j];
        }
    }

    for(i=0; i<2; i++)
    {
        for(j=0; j<64; j++)
        {
            pi->ScalingList32x32[i][j] =
                pps->scaling_list.scaling_lists_32x32[i][j];
        }
    }

    for(i=0; i<6; i++)
    {
        pi->ScalingListDCCoeff16x16[i] =
            pps->scaling_list.scaling_list_dc_coef_minus8_16x16[i] + 8;
    }

    for(i=0; i<2; i++)
    {
        pi->ScalingListDCCoeff32x32[i] =
            pps->scaling_list.scaling_list_dc_coef_minus8_32x32[i] + 8;
    }

    return 0;
}

static int update_picture_info_vps()
{
    return 0;
}

/*
   8.3.1 Decoding process for picture order count

   Per the Specification, "Output of this process is PicOrderCntVal, the
   picture order count of the current picture".

   - Store PicOrderCntVal in pi->CurrPicOrderCntVal.
   - Storesslice_pic_order_cnt_lsb in context->current_slice_pic_order_cnt_lsb.
   - Stash prevPicOrderCntLsb and prevPicOrderCntMsb in the context for
   future use.

 */
static void decode_picture_order_count(
    VdpPictureInfoHEVC *pi,
    hevc_decoder_context *context,
    GstH265SliceHdr *slice,
    GstH265NalUnit *nalu)
{
    int PicOrderCntMsb = 0;
    int MaxPicOrderCntLsb = 1<<(pi->log2_max_pic_order_cnt_lsb_minus4 + 4);

    if(pi->IDRPicFlag)
    {
        context->prevPicOrderCntLsb = 0;
        context->prevPicOrderCntMsb = 0;
    }

    if(pi->RAPPicFlag && context->NoRaslOutputFlag)
    {
        PicOrderCntMsb = 0;
    }
    /* (8-1) */
    else if((slice->pic_order_cnt_lsb < context->prevPicOrderCntLsb) &&
            ((context->prevPicOrderCntLsb - slice->pic_order_cnt_lsb)
             >= (MaxPicOrderCntLsb/2)))
    {
        PicOrderCntMsb = context->prevPicOrderCntMsb + MaxPicOrderCntLsb;
    }
    else if((slice->pic_order_cnt_lsb > context->prevPicOrderCntLsb) &&
            ((slice->pic_order_cnt_lsb - context->prevPicOrderCntLsb)
             > (MaxPicOrderCntLsb/2)))
    {
        PicOrderCntMsb = context->prevPicOrderCntMsb - MaxPicOrderCntLsb;
    }
    else
    {
        PicOrderCntMsb = context->prevPicOrderCntMsb;
    }

    /* (8-2) */
    pi->CurrPicOrderCntVal = slice->pic_order_cnt_lsb + PicOrderCntMsb;

    /* Store the slice_pic_order_cnt_lsb for (8-6) later in the process. */
    context->current_slice_pic_order_cnt_lsb = slice->pic_order_cnt_lsb;

    if((nalu->temporal_id_plus1 - 1) == 0)
    {
        context->prevPicOrderCntLsb = slice->pic_order_cnt_lsb;
        context->prevPicOrderCntMsb = PicOrderCntMsb;
    }
}

/*
   8.3.3.2 Generation of one unavailable reference picture
   Fills the VdpVideoSurface in question with data as per the Specification.
 */
/* TODO - Where to put this generated picture? In the DPB? */
/* RESOLVED - Yes. Use an existing unused frame and put in the DPB. WIP. */
static void generate_unavailable_reference_picture(
    VdpPictureInfoHEVC *pi,
    VdpVideoSurface *surface
)
{
    /* TODO - Compatibility with different chroma types. */
    VdpYCbCrFormat format = VDP_YCBCR_FORMAT_NV12;
    uint32_t width = pi->pic_width_in_luma_samples;
    uint32_t height = pi->pic_height_in_luma_samples;
    uint8_t *luma_data = NULL, *chroma_data = NULL;
    const void* source_data[2] = { NULL, NULL };
    const uint32_t source_pitches[2] = { width, width/2 } ;

    // malloc some arrays
    luma_data = malloc(width * height);
    chroma_data = malloc(width * height / 2);
    // fill them
    // set source data
    source_data[0] = luma_data;
    source_data[1] = chroma_data;
    //VdpVideoSurfaceQueryGetPutBitsYCbCrCapabilities
    //VdpVideoSurfacePutBitsYCbCr
    vdp_video_surface_put_bits_y_cb_cr(
        *surface,
        format,
        &source_data[0],
        &source_pitches[0]
    );

    free(luma_data);
    free(chroma_data);
}

/*
   Helper function for RPS derivation process in (8-6) and (8-7). Implements:
   "if there is a (maybe short term) reference picture picX in the DPB with
   (slice_pic_order_cnt_lsb or PicOrderCntVal" equal to some particular POC".

   Walks the DPB array and related arrays in hevc_decoder_context.

   Returns the index of the picture in the DPB array, pi->RefPics[], that
   matches the requested poc value, or -1 if one is not found. Callers shall
   interpret a return value of -1 as "no reference picture".
 */
static int32_t find_pic_in_dpb_with_poc(
    VdpPictureInfoHEVC *pi,
    hevc_decoder_context *context,
    int32_t poc,
    uint8_t short_term_only,
    uint8_t lsb_only)
{
    int i;
    uint8_t usage_mask;
    int32_t *poc_list;

    usage_mask = USED_FOR_SHORT_TERM_REFERENCE;

    if(!short_term_only)
        usage_mask |= USED_FOR_LONG_TERM_REFERENCE;

    if(lsb_only)
        poc_list = context->dpb_slice_pic_order_cnt_lsb;
    else
        poc_list = pi->PicOrderCntVal;

    for(i=0; i < HEVC_MAX_REFERENCES && i < context->MaxDpbSize; i++)
    {
        if(poc_list[i] == poc &&
                (context->dpb_reference_values[i] & usage_mask))
            return i;
    }

    fprintf(stderr, "NOTICE: Unable to find pic in DPB with POC: %d\n", poc);
    return -1;
}

/* TODO - Break out H265 spec handling code into a separate file. */
/*
   8.3.2 Decoding process for reference picture set

   This process generates five lists of picture order counts:
   PocStCurrBefore, PocStCurrAfter, PocStFoll,
   PocLtCurr, and PocLtFoll.

   These five lists have these corresponding numbers of elements:
   NumPocStCurrBefore, NumPocStCurrAfter, NumPocStFoll,
   NumPocLtCurr, NumPocLtFoll.

   These five lists (and their corresponding numbers of elements) are then
   used to generate the five reference picture set (RPS) lists of the current
   picture:
   RefPicSetStCurrBefore, RefPicSetStCurrAfter, RefPicSetStFoll,
   RefPicSetLtCurr, RefPicSetLtFoll.

   As a side effect, this function sets the dpb_reference_values array in
   hevc_decoder_context, marking whether or not particular DPB entries are
   used for reference.

   For VDPAU playback, we do not need to pass in "Foll" lists as they are not
   helpful for decoding the current picture. The "Curr" lists are stored in
   VdpPictureInfoHEVC and passed to the VDPAU implementation. The "Foll" lists
   are stored locally, in this implementation's hevc_decoder_context.

Q: What per-picture state do we need to track in the player? Perhaps an
|  array of POC values for pictures in the DPB, er, RefPics[] array?
A: Per picture player state is stored in hevc_decoder_context.

Q: The caller needs to make sure we've got the correct SPS...
A: Not quite. We just need to make sure that CurrRpsIdx is being handled
correctly.
 */
static void decode_reference_picture_set(
    VdpPictureInfoHEVC *pi,
    hevc_decoder_context *context,
    GstH265SliceHdr *slice,
    GstH265SPS *sps
)
{
    int32_t PocStCurrBefore[16];
    int32_t PocStCurrAfter[16];
    int32_t PocStFoll[16];
    int32_t PocLtCurr[16];
    int32_t PocLtFoll[16];

    uint8_t CurrDeltaPocMsbPresentFlag[16];
    uint8_t FollDeltaPocMsbPresentFlag[16];

    uint8_t NumPocStCurrBefore;
    uint8_t NumPocStCurrAfter;
    uint8_t NumPocStFoll;
    uint8_t NumPocLtCurr;
    uint8_t NumPocLtFoll;

    uint8_t NumPocTotalCurr;

    /*
       VDPAU provides these three reference picture sets in VdpPictureInfoHEVC:
       int8_t RefPicSetStCurrBefore[8];
       int8_t RefPicSetStCurrAfter[8];
       int8_t RefPicSetLtCurr[8];

       Store remaining two Foll reference picture sets in hevc_decoder_context:
       int8_t RefPicSetStFoll[8];
       int8_t RefPicSetLtFoll[8];
     */

    int i, j, k;
    uint8_t CurrRpsIdx;
    GstH265ShortTermRefPicSet *stRPS = NULL;
    int pocLt, UsedByCurrPicLt;
    int MaxPicOrderCntLsb = 1<<(pi->log2_max_pic_order_cnt_lsb_minus4 + 4);
    uint16_t pictures_in_use = 0;

    if(pi->IDRPicFlag && context->NoRaslOutputFlag)
    {
        for(i=0; i<HEVC_MAX_REFERENCES; i++)
        {
            context->dpb_reference_values[i] = UNUSED_FOR_REFERENCE;
        }
    }

    /* (8-5) */
    /* (7-43) for calculation of NumPocTotalCurr */
    for(i = 0; i < 16; i++)
    {
        PocStCurrBefore[i] = 0;
        PocStCurrAfter[i] = 0;
        PocStFoll[i] = 0;
        PocLtCurr[i] = 0;
        PocLtFoll[i] = 0;
    }
    NumPocStCurrBefore = 0;
    NumPocStCurrAfter = 0;
    NumPocStFoll = 0;
    NumPocLtCurr = 0;
    NumPocLtFoll = 0;

    NumPocTotalCurr = 0;

    if(!pi->IDRPicFlag)
    {
        if (slice->short_term_ref_pic_set_sps_flag)
        {
            CurrRpsIdx = slice->short_term_ref_pic_set_idx;
            stRPS = &sps->short_term_ref_pic_set[CurrRpsIdx];
        }
        else
        {
            CurrRpsIdx = sps->num_short_term_ref_pic_sets;
            stRPS = &slice->short_term_ref_pic_sets;
        }

        for(i=0, j=0, k=0; i < stRPS->NumNegativePics; i++)
        {
            if(stRPS->UsedByCurrPicS0[i])
            {
                PocStCurrBefore[j++] =
                    pi->CurrPicOrderCntVal + stRPS->DeltaPocS0[i];
                NumPocTotalCurr++;
            }
            else
                PocStFoll[k++] =
                    pi->CurrPicOrderCntVal + stRPS->DeltaPocS0[i];
        }
        NumPocStCurrBefore = j;

        for(i=0, j=0; i < stRPS->NumPositivePics; i++)
        {
            if(stRPS->UsedByCurrPicS1[i])
            {
                PocStCurrAfter[j++] =
                    pi->CurrPicOrderCntVal + stRPS->DeltaPocS1[i];
                NumPocTotalCurr++;
            }
            else
                PocStFoll[k++] = pi->CurrPicOrderCntVal + stRPS->DeltaPocS1[i];
        }
        NumPocStCurrAfter = j;
        NumPocStFoll = k;

        for(i=0, j=0, k=0;
                i < slice->num_long_term_sps + slice->num_long_term_pics;
                i++)
        {
            /* 7.4.7.1 PocLsbLt[i] UsedByCurrPicLt[i] */
            if(i < slice->num_long_term_sps)
            {
                pocLt = sps->lt_ref_pic_poc_lsb_sps[slice->lt_idx_sps[i]];
                UsedByCurrPicLt =
                    sps->used_by_curr_pic_lt_sps_flag[slice->lt_idx_sps[i]];
            }
            else
            {
                pocLt = slice->poc_lsb_lt[i];
                UsedByCurrPicLt = slice->used_by_curr_pic_lt_flag[i];
            }

            if(slice->delta_poc_msb_present_flag[i])
                pocLt += pi->CurrPicOrderCntVal
                         - (slice->delta_poc_msb_cycle_lt[i]*MaxPicOrderCntLsb)
                         - slice->pic_order_cnt_lsb;

            if(UsedByCurrPicLt)
            {
                PocLtCurr[j] = pocLt;
                CurrDeltaPocMsbPresentFlag[j++] =
                    slice->delta_poc_msb_present_flag[i];
                NumPocTotalCurr++;
            }
            else
            {
                PocLtFoll[k] = pocLt;
                FollDeltaPocMsbPresentFlag[k++] =
                    slice->delta_poc_msb_present_flag[i];
            }
        }
        NumPocLtCurr = j;
        NumPocLtFoll = k;
    }

    /* TODO - Implement error checking as defined on p.96-97 */

    /* Derivation process for RPS and picture marking. */

    /* Step 1. */
    /* (8-6) Generation of long term reference picture sets. */
    for(i=0; i < NumPocLtCurr; i++)
    {
        if(!CurrDeltaPocMsbPresentFlag[i])
        {
            pi->RefPicSetLtCurr[i] =
                find_pic_in_dpb_with_poc(pi, context, PocLtCurr[i], 0, 1);
        }
        else
        {
            pi->RefPicSetLtCurr[i] =
                find_pic_in_dpb_with_poc(pi, context, PocLtCurr[i], 0, 0);
        }
    }
    for(i=0; i < NumPocLtFoll; i++)
    {
        if(!FollDeltaPocMsbPresentFlag[i])
        {
            context->RefPicSetLtFoll[i] =
                find_pic_in_dpb_with_poc(pi, context, PocLtFoll[i], 0, 1);
        }
        else
        {
            context->RefPicSetLtFoll[i] =
                find_pic_in_dpb_with_poc(pi, context, PocLtFoll[i], 0, 0);
        }
    }

    /* Step 2. Marking of long term reference pictures. */
    for(i=0; i < NumPocLtCurr; i++)
    {
        if(pi->RefPicSetLtCurr[i] >= 0)
        {
            context->dpb_reference_values[pi->RefPicSetLtCurr[i]] =
                USED_FOR_LONG_TERM_REFERENCE;
            pictures_in_use |= 1 << pi->RefPicSetLtCurr[i];
        }
    }
    for(i=0; i < NumPocLtFoll; i++)
    {
        if(context->RefPicSetLtFoll[i] >= 0)
        {
            context->dpb_reference_values[context->RefPicSetLtFoll[i]] =
                USED_FOR_LONG_TERM_REFERENCE;
            pictures_in_use |= 1 << context->RefPicSetLtFoll[i];
        }
    }

    /* Step 3. */
    /* (8-7) Generation of short term reference picture sets. */
    for(i=0; i < NumPocStCurrBefore; i++)
    {
        pi->RefPicSetStCurrBefore[i] =
            find_pic_in_dpb_with_poc(pi, context, PocStCurrBefore[i], 1, 0);
        if(pi->RefPicSetStCurrBefore[i] >= 0)
            pictures_in_use |= 1 << pi->RefPicSetStCurrBefore[i];
    }

    for(i=0; i < NumPocStCurrAfter; i++)
    {
        pi->RefPicSetStCurrAfter[i] =
            find_pic_in_dpb_with_poc(pi, context, PocStCurrAfter[i], 1, 0);
        if(pi->RefPicSetStCurrAfter[i] >= 0)
            pictures_in_use |= 1 << pi->RefPicSetStCurrAfter[i];
    }

    for(i=0; i < NumPocStFoll; i++)
    {
        context->RefPicSetStFoll[i] =
            find_pic_in_dpb_with_poc(pi, context, PocStFoll[i], 1, 0);
        if(context->RefPicSetStFoll[i] >= 0)
            pictures_in_use |= 1 << context->RefPicSetStFoll[i];
    }

    /* Step 4. Marking of unused reference pictures. */
    /* Implement this using a bit mask which we set previously. */
    for(i=0; i < context->MaxDpbSize; i++)
        if(!(pictures_in_use & (1 << i)))
            context->dpb_reference_values[i] = UNUSED_FOR_REFERENCE;

    /* TODO - Implement error checking as defined on p.98-99 */
    context->NumPocStFoll = NumPocStFoll;
    context->NumPocLtFoll = NumPocLtFoll;

    pi->NumPocStCurrBefore = NumPocStCurrBefore;
    pi->NumPocStCurrAfter = NumPocStCurrAfter;
    pi->NumPocLtCurr = NumPocLtCurr;

    pi->NumPocTotalCurr = NumPocTotalCurr;

    if(stRPS)
        pi->NumDeltaPocsOfRefRpsIdx = stRPS->NumDeltaPocs;
    else
        pi->NumDeltaPocsOfRefRpsIdx = 0;
}

/*
    Update decoder state with the information contained in an incoming slice
    header.

    Implements:
    8.1 General decoding process
    Generates upper-case variables from clause 7 as required.
    8.2 NAL unit decoding process
    Works together with gst_h265_parser_parse_slice_hdr to parse NAL unit.
 */
static void update_picture_info_slice_header(
    VdpPictureInfoHEVC *pi,
    hevc_decoder_context *context,
    GstH265SliceHdr *slice,
    GstH265NalUnit *nalu,
    GstH265SPS *sps
)
{
    int stRpsIdx, RefRpsIdx;
    /* int UseAltCpbParamsFlag = 0; - NOT USED */
    int HandleCraAsBlaFlag = 0;

    context->NoRaslOutputFlag = 1;

    /*
       7.4.7.1 General slice segment header semantics

       The variable CurrRpsIdx is derived as follows:
       – If short_term_ref_pic_set_sps_flag is equal to 1, CurrRpsIdx is set
         equal to short_term_ref_pic_set_idx.
       – Otherwise, CurrRpsIdx is set equal to num_short_term_ref_pic_sets.
     */
    if(slice->short_term_ref_pic_set_sps_flag)
        pi->CurrRpsIdx = slice->short_term_ref_pic_set_idx;
    else
        pi->CurrRpsIdx = pi->num_short_term_ref_pic_sets;

    if(nalu->type == GST_H265_NAL_SLICE_IDR_W_RADL ||
            nalu->type == GST_H265_NAL_SLICE_IDR_N_LP)
        pi->IDRPicFlag = 1;
    else
        pi->IDRPicFlag = 0;

    if(nalu->type >= GST_H265_NAL_SLICE_BLA_W_LP &&
            nalu->type <= 23) /* RSV_IRAP_VCL23, undefined in GStreamer */
        pi->RAPPicFlag = 1;
    else
        pi->RAPPicFlag = 0;

    /*
       7.4.8 Short-term reference picture set semantics

       NumDeltaPocsOfRefRpsIdx

       The variable RefRpsIdx is derived as follows:
       RefRpsIdx = stRpsIdx − ( delta_idx_minus1 + 1 ) (7-45)
     */
    if(slice->short_term_ref_pic_set_sps_flag)
    {
        /* Do short term RPS stuff based on what is in SPS. */
        pi->NumDeltaPocsOfRefRpsIdx = 0; /* not used */
    }
    else
    {
        /* Use slice segment header for SPS stuff. */
        stRpsIdx = sps->num_short_term_ref_pic_sets;
        RefRpsIdx = stRpsIdx -
                    (sps->short_term_ref_pic_set[stRpsIdx].delta_idx_minus1+1);
        pi->NumDeltaPocsOfRefRpsIdx =
            sps->short_term_ref_pic_set[RefRpsIdx].NumDeltaPocs;
    }

    /*
       7.4.7.2 Reference picture list modification semantics
     */
    pi->NumShortTermPictureSliceHeaderBits =
        slice->NumShortTermPictureSliceHeaderBits;
    pi->NumLongTermPictureSliceHeaderBits =
        slice->NumLongTermPictureSliceHeaderBits;

    /* 8.1 Decoding process for a coded picture
       with nuh_layer_id equal to 0        */
    if (nalu->type == GST_H265_NAL_SLICE_BLA_W_LP ||
            nalu->type == GST_H265_NAL_SLICE_CRA_NUT)
    {
        /* TODO - Handle UseAltCpbParamsFlag. */
        //UseAltCpbParamsFlag = 0;
    }

    if (nalu->type == GST_H265_NAL_SLICE_IDR_W_RADL ||
            nalu->type == GST_H265_NAL_SLICE_IDR_N_LP   ||
            nalu->type == GST_H265_NAL_SLICE_BLA_W_LP   ||
            nalu->type == GST_H265_NAL_SLICE_BLA_W_RADL ||
            nalu->type == GST_H265_NAL_SLICE_BLA_N_LP   ||
            /* first picture in bitstream in decoding order */
            /* first picture after end of stream */
            context->IsFirstPicture)
    {
        context->NoRaslOutputFlag = 1;
    }
    /* TODO - Provide ability to set HandleCraAsBlaFlag by external means. */
    else if(HandleCraAsBlaFlag)
    {
        context->NoRaslOutputFlag = HandleCraAsBlaFlag;
    }
    else
    {
        HandleCraAsBlaFlag = 0;
        context->NoRaslOutputFlag = 0;
    }
}

/*
   C.3.2 Removal of pictures from the DPB

   Walks the DPB, marking pictures as UNUSED_FOR_REFERENCE. Modifies state
   variables in hevc_decoder_context.

   Must be called immediately after decode_reference_picture_set() as noted
   in the Specification.
 */
static void remove_pictures_from_dpb(
    VdpPictureInfoHEVC *pi,
    hevc_decoder_context *context,
    GstH265SliceHdr *slice,
    GstH265NalUnit *nalu)
{
    int i;

    if(pi->IDRPicFlag &&
            context->NoRaslOutputFlag)
    {
        /* 1. Determine NoOutputOfPriorPicsFlag. */
        if(nalu->type == GST_H265_NAL_SLICE_CRA_NUT &&
                !(context->IsFirstPicture))
            context->NoOutputOfPriorPicsFlag = 1;
        /* TODO - NoOutputOfPriorPicsFlag may be set if
        pic_width_in_luma_samples,
           pic_height_in_luma_samples, or
           sps_max_dec_pic_buffering_minus1[HighestTid] have changed.
           This is not implemented here. */
        else if(context->IsFirstPicture)
            /* Not defined in Specification but a convenient place
               to handle picture 0 */
            context->NoOutputOfPriorPicsFlag = 1;
        else
            context->NoOutputOfPriorPicsFlag =
                slice->no_output_of_prior_pics_flag;

        /* 2. Apply NoOutputOfPriorPicsFlag. */
        if(context->NoOutputOfPriorPicsFlag)
        {
            for(i=0; i<HEVC_MAX_REFERENCES; i++)
            {
                context->dpb_reference_values[i] = UNUSED_FOR_REFERENCE;
                context->PicOutputFlag[i] = 0;
                /* Not required in Specification but convenient to do
                this here. */
                pi->PicOrderCntVal[i] = 0;
                context->dpb_slice_pic_order_cnt_lsb[i] = 0;
                pi->RefPics[i] = VDP_INVALID_HANDLE;
            }
            context->dpb_fullness = 0;
        }
    }

    /* Remove pictures from DPB. */
    for(i=0; i<HEVC_MAX_REFERENCES; i++)
    {
        if(pi->RefPics[i] != VDP_INVALID_HANDLE &&
                context->dpb_reference_values[i] == UNUSED_FOR_REFERENCE &&
                context->PicOutputFlag[i] == 0
                /* || timing condition - not implemented */
          )
        {
            pi->RefPics[i] = VDP_INVALID_HANDLE;
            context->dpb_fullness--;
            if(context->dpb_fullness < 0)
                printf("ERROR: dpb_fullness should not be negative!\n");
        }
    }
}

/*
   8.3.3 Decoding process for generating unavailable pictures

   Depends on generate_unavailable_reference_picture() to actually fill a
   VdpVideoSurface with luma and chroma data as specified in 8.3.3.2.

 */
static void generate_unavailable_reference_pictures(
    VdpPictureInfoHEVC *pi,
    hevc_decoder_context *context,
    GstH265NalUnit *nalu)
{
    if(nalu->type == GST_H265_NAL_SLICE_BLA_W_LP ||
            nalu->type == GST_H265_NAL_SLICE_BLA_W_RADL ||
            nalu->type == GST_H265_NAL_SLICE_BLA_N_LP ||
            (nalu->type == GST_H265_NAL_SLICE_CRA_NUT &&
             context->NoRaslOutputFlag))
    {
        int i;

        for(i=0; i < context->NumPocStFoll; i++)
        {
            /* TODO: Unimplemented. */
            if(0)
                generate_unavailable_reference_picture(pi, &pi->RefPics[15]);
        }
        for(i=0; i < context->NumPocLtFoll; i++)
        {
            /* TODO: Unimplemented. */
            if(0)
                generate_unavailable_reference_picture(pi, &pi->RefPics[15]);
        }
    }
}

/*
   C.3.4 Current decoded picture marking and storage

   Walks the DPB looking for an unused entry. Marks it as "used for short term
   reference" and returns the index. Returns -1 in case of error.
 */

static int8_t get_decoded_picture_index(hevc_decoder_context *context)
{
    int i;

    /* Find a place for the decoded picture to go. */
    for(i=0; i < HEVC_MAX_REFERENCES && i < context->MaxDpbSize; i++)
    {
        if(context->dpb_reference_values[i] == UNUSED_FOR_REFERENCE)
        {
            context->dpb_reference_values[i] = USED_FOR_SHORT_TERM_REFERENCE;
            context->dpb_fullness++;
            return i;
        }
    }

    return -1;
}

/*
   8.1 decoding process step 2 bullet 4
   Calculation of PicOutputFlag
 */
static void calculate_PicOutputFlag(
    hevc_decoder_context *context,
    GstH265SliceHdr *slice,
    GstH265NalUnit *nalu,
    int8_t target_index)
{
    if((nalu->type == GST_H265_NAL_SLICE_RASL_N ||
            nalu->type == GST_H265_NAL_SLICE_RASL_R) &&
            context->NoRaslOutputFlag)
    {
        context->PicOutputFlag[target_index] = 0;
    }
    else
    {
        context->PicOutputFlag[target_index] = slice->pic_output_flag;
    }
}

static int update_picture_info_sei(
    VdpPictureInfoHEVC *pi,
    GstH265SEIMessage *sei
)
{
    /* TODO: Implement as needed. */
    return 0;
}
static int errorDetected = 0;

static void ErrorNotifier(VdpDevice device, void *data)
{
    printf(" Error Notifier called!\n");
    errorDetected = 1;
}

static VdpOutputSurface WaitForSurface()
{
    VdpOutputSurface outputSurface;
    VdpStatus vdp_st;
    VdpTime displayed_at;
    VdpPresentationQueueStatus status;
    int i;

    outputSurface = outputSurfaces[displayFrameNumber % NUM_OUTPUT_SURFACES];
    displayFrameNumber++;

    for (i = 0; i < num_win_ids; i++)
    {
        vdp_st = vdp_presentation_queue_block_until_surface_idle(
                     /* inputs */
                     vdp_flip_queue[i], /* presentation_queue */
                     outputSurface, /* surface */
                     /* output */
                     &displayed_at /* first_presentation_time */
                 );
        CHECK_STATE
    }

    vdp_st = vdp_presentation_queue_query_surface_status(
                 /* inputs */
                 vdp_flip_queue[0], /* presentation_queue */
                 outputSurface, /* surface */
                 /* outputs */
                 &status, /* status */
                 &displayed_at /* first_presentation_time */
             );
    CHECK_STATE

#if DEBUG_TIMES
    if (
        (DEBUG_TIMES & DEBUG_TIMES_PRINT_DISPLAYED_AT)
        ||
        (
            (DEBUG_TIMES & DEBUG_TIMES_PRINT_DISPLAYED_AT_LATE)
            &&
            (displayed_at < surf_entries[outputSurface].schedule_time)
        )
    )
    {
        printf(
            "Displayed %u at %" PRIu64 " (+%" PRId64 ") [%d]\n",
            outputSurface,
            displayed_at,
            displayed_at - surf_entries[outputSurface].schedule_time,
            (int)status
        );
    }
#endif

#if DEBUG_TIMES & DEBUG_TIMES_PRINT_STREAM_TIME
    if (surf_entries[outputSurface].is_start_of_stream)
    {
        stream_start_time[surf_entries[outputSurface].stream_index] =
            displayed_at;
        surf_entries[outputSurface].is_start_of_stream = 0;
    }

    if (surf_entries[outputSurface].is_end_of_stream)
    {
        double start_time =
            stream_start_time[surf_entries[outputSurface].stream_index];
        double elapsed = (double)displayed_at - (double)start_time;

        printf("Display took  %f seconds\n", elapsed * 1e-9);

        surf_entries[outputSurface].is_end_of_stream = 0;
    }
#endif

    return outputSurface;
}

static void RecalcOutputRect()
{
    uint32_t screenWidth, screenHeight;
    float vidAspect, monAspect, factor;

    win_x11_poll_events();
    screenWidth = win_x11_get_width(0);
    if (screenWidth > MAX_WIN_WIDTH)
    {
        screenWidth = MAX_WIN_WIDTH;
    }
    screenHeight = win_x11_get_height(0);
    if (screenHeight > MAX_WIN_HEIGHT)
    {
        screenHeight = MAX_WIN_HEIGHT;
    }

    outRect.x0 = 0;
    outRect.x1 = screenWidth;
    outRect.y0 = 0;
    outRect.y1 = screenHeight;

    /* This is not the right way to get the aspect ratios */
    vidAspect = (float)vid_width / (float)vid_height;
    monAspect = (float)screenWidth / (float)screenHeight;

    if(vidAspect > monAspect)    /* letter box */
    {
        factor = (1.0 - (monAspect / vidAspect)) * 0.5;
        factor *= (float)screenHeight;

        outRectVid.x0 = 0;
        outRectVid.x1 = screenWidth;
        outRectVid.y0 = factor;
        outRectVid.y1 = screenHeight - factor;
    }
    else
    {
        factor = (1.0 - (vidAspect / monAspect)) * 0.5;
        factor *= (float)screenWidth;

        outRectVid.x0 = factor;
        outRectVid.x1 = screenWidth - factor;
        outRectVid.y0 = 0;
        outRectVid.y1 = screenHeight;
    }
}

static void Flip(
    VdpOutputSurface outputSurface,
    uint64_t        period
)
{
    VdpTime this_time;
    VdpStatus vdp_st;
    int i;
#if DEBUG_TIMES
    VdpTime last_time = gtime;
#endif

    if (period)
    {
        if (!gtime)
        {
            /* have it start in 1/4 sec */
            vdp_st = vdp_presentation_queue_get_time(
                         /* input */
                         vdp_flip_queue[0], /* presentation_queue */
                         /* output */
                         &gtime /* current_time */
                     );
            CHECK_STATE
            gtime += 250000000;
#if DEBUG_TIMES
            last_time = gtime;
#endif
        }
        else
        {
            gtime += period;
        }
        this_time = gtime;
    }
    else
    {
        this_time = 0;
    }

#if DEBUG_TIMES
#if DEBUG_TIMES & DEBUG_TIMES_PRINT_SCHEDULED_AT
    printf(
        "Schedule  %u at %" PRIu64 " (+%" PRId64 ")\n",
        outputSurface,
        this_time,
        this_time - last_time
    );
#endif

    if (is_stream_start)
    {
        surf_entries[outputSurface].is_start_of_stream = 1;
        surf_entries[outputSurface].stream_index = stream_start_time_index;
        is_stream_start = 0;
    }
    surf_entries[outputSurface].schedule_time = this_time;
    last_surface_displayed = outputSurface;
#endif

    for (i = 0; i < num_win_ids; i++)
    {
        vdp_st = vdp_presentation_queue_display(
                     vdp_flip_queue[i], /* presentation_queue */
                     outputSurface, /* surface */
                     outRect.x1, /* clip_width */
                     outRect.y1, /* clip_height */
                     this_time /* earliest_presentation_time */
                 );
        CHECK_STATE
    }
}

static void MoveQueue(void)
{
    int i;

    if (displayQueue[0] != -1)
    {
        inUse[displayQueue[0]] &= ~QUEUED_FOR_DISPLAY;
    }

    for (i = 0; i < NUM_OUTPUT_SURFACES - 1; i++)
    {
        displayQueue[i] = displayQueue[i+1];
    }

    displayQueue[NUM_OUTPUT_SURFACES-1] = -1;
}

static void DisplayFrame(
    VdpPictureInfoHEVC *pi,
    uint64_t period,
    int8_t target_index)
{
    VdpOutputSurface outputSurface;
    VdpStatus vdp_st;

    outputSurface = WaitForSurface();

    RecalcOutputRect();

    /*

       VDPAU implementations must allow VDP_VIDEO_MIXER_PICTURE_STRUCTURE_FRAME
       to work correctly here. Players should not need to use a hack here by
       declaring this frame to be a top or bottom field.

       For VDPAU HEVC decoding, video_surface_past and video_surface_future
       should be NULL for progressive frames. Presentation of interlaced
       frames will work as for formats with native interlaced decoding but
       note that each field will be an HEVC frame in its own right.

     */

    vdp_st = vdp_video_mixer_render(
                 videoMixer, /* mixer */
                 VDP_INVALID_HANDLE, /* background_surface */
                 0, /* background_source_rect */
                 /* current_picture_structure*/
                 VDP_VIDEO_MIXER_PICTURE_STRUCTURE_FRAME,
                 0, /* video_surface_past_count */
                 NULL, /* video_surface_past */
                 pi->RefPics[target_index], /* video_surface_current */
                 0, /* video_surface_future_count */
                 NULL, /* video_surface_future */
                 NULL, /* video_source_rect */
                 outputSurface, /* destination_surface */
                 &outRect, /* destination_rect */
                 &outRectVid, /* destination_video_rect */
                 0, /* layer_count */
                 NULL /* layers */
             );
    CHECK_STATE

    Flip(outputSurface, period);
}

static void CreateVdpapiObjects(
    VdpPictureInfoHEVC *pi,
    hevc_decoder_context *context,
    int bits_10)
{
    int i;
    VdpStatus vdp_st;

    vdp_st = win_x11_init_vdpau_procs();
    CHECK_STATE

    for (i = 0; i < num_win_ids; i++)
    {
        vdp_st = win_x11_init_vdpau_flip_queue(i, 0);
        CHECK_STATE
    }

    // Object creation

    vdp_st = vdp_preemption_callback_register(
                 vdp_device, /* device */
                 ErrorNotifier, /* callback */
                 NULL /* context */
             );

    vid_width = pi->pic_width_in_luma_samples;
    vid_height = pi->pic_height_in_luma_samples;

    vdp_st = vdp_decoder_create(
                 /* inputs */
                 vdp_device, /* device */
                 bits_10
                 ? VDP_DECODER_PROFILE_HEVC_MAIN_10
                 : VDP_DECODER_PROFILE_HEVC_MAIN, /* profile */
                 vid_width, /* width */
                 vid_height, /* height */
                 HEVC_MAX_REFERENCES, /* max_references */
                 /* output */
                 &decoder
             );
    CHECK_STATE

    for(i = 0; i < HEVC_MAX_REFERENCES; i++)
    {
        vdp_st = vdp_video_surface_create(
                     /* inputs */
                     vdp_device, /* device */
                     VDP_CHROMA_TYPE_420, /* chroma_type */
                     vid_width, /* width */
                     vid_height, /* height */
                     /* output */
                     &(context->scratch_frames[i]) /* surface */
                 );
        CHECK_STATE
        serialNumbers[i] = 0;  /* init surface accounting in this loop */
        inUse[i] = 0;
    }

    for(i = 0; i < NUM_OUTPUT_SURFACES; i++)
    {
        displayQueue[i] = -1;
    }

    /***********  initialize display *********/

    for(i = 0; i < NUM_OUTPUT_SURFACES; i++)
    {
        vdp_st = vdp_output_surface_create(
                     /* inputs */
                     vdp_device, /* device */
                     bits_10 ?
                     VDP_RGBA_FORMAT_R10G10B10A2 :
                     VDP_RGBA_FORMAT_B8G8R8A8, /* rgba_format */
                     MAX_WIN_WIDTH, /* width */
                     MAX_WIN_HEIGHT, /* height */
                     /* output */
                     &outputSurfaces[i] /* surface */
                 );
        CHECK_STATE
        vdp_st = vdp_output_surface_render_output_surface(
                     outputSurfaces[i], /* destination_surface */
                     NULL, /* destination_rect */
                     VDP_INVALID_HANDLE, /* source_surface */
                     NULL, /* source_rect */
                     NULL, /* colors */
                     NULL, /* blend_state */
                     0 /* flags */
                 );
        CHECK_STATE
    }

    {
        // Order is important in code below, where enables are set.
        VdpVideoMixerFeature features[] =
        {
            VDP_VIDEO_MIXER_FEATURE_NOISE_REDUCTION,
            VDP_VIDEO_MIXER_FEATURE_SHARPNESS,
            VDP_VIDEO_MIXER_FEATURE_INVERSE_TELECINE,
            VDP_VIDEO_MIXER_FEATURE_DEINTERLACE_TEMPORAL,
            VDP_VIDEO_MIXER_FEATURE_DEINTERLACE_TEMPORAL_SPATIAL
        };
        VdpBool feature_enables[] =
        {
            VDP_FALSE,
            VDP_FALSE,
            VDP_FALSE,
            VDP_FALSE,
            VDP_FALSE
        };

        uint32_t vdp_width = vid_width;
        uint32_t vdp_height = vid_height;
        VdpChromaType vdp_chroma_type = VDP_CHROMA_TYPE_420;

        VdpVideoMixerParameter parameters[] =
        {
            VDP_VIDEO_MIXER_PARAMETER_VIDEO_SURFACE_WIDTH,
            VDP_VIDEO_MIXER_PARAMETER_VIDEO_SURFACE_HEIGHT,
            VDP_VIDEO_MIXER_PARAMETER_CHROMA_TYPE
        };
        void const * parameter_values[ARSIZE(parameters)] =
        {
            &vdp_width,
            &vdp_height,
            &vdp_chroma_type
        };

        vdp_st = vdp_video_mixer_create(
                     vdp_device,
                     ARSIZE(features),
                     features,
                     ARSIZE(parameters),
                     parameters,
                     parameter_values,
                     &videoMixer
                 );
        CHECK_STATE

        vdp_st = vdp_video_mixer_set_feature_enables(
                     videoMixer, /* mixer */
                     ARSIZE(features), /* feature_count */
                     features, /* features */
                     feature_enables /* feature_enables */
                 );
        CHECK_STATE
    }
}

static void DestroyVdpapiObjects(
    VdpPictureInfoHEVC *pi,
    hevc_decoder_context *context)
{
    int i;
    VdpStatus vdp_st;

    vdp_st = vdp_preemption_callback_register(vdp_device, NULL, NULL);
    CHECK_STATE

    vdp_st = vdp_video_mixer_destroy(
                 videoMixer
             );
    CHECK_STATE

    for (i = 0; i < NUM_OUTPUT_SURFACES; i++)
    {
        vdp_st = vdp_output_surface_destroy(
                     outputSurfaces[i]
                 );
        CHECK_STATE
    }

    for (i = 0; i < HEVC_MAX_REFERENCES; i++)
    {
        vdp_st = vdp_video_surface_destroy(context->scratch_frames[i]);
        CHECK_STATE
    }

    vdp_st = vdp_decoder_destroy(
                 decoder
             );
    CHECK_STATE

    vdp_st = win_x11_fini_vdpau_flip_queue(0);
    CHECK_STATE

    vdp_st = win_x11_fini_vdpau_procs();
    CHECK_STATE
}


int main(int argc, char *argv[])
{
    FILE *file;
    GstH265ParserResult result;
    int nals = 0;
    int i, nal_length = 0, bits_10=0;
    uint8_t loop = 0;
    float factor;
    uint64_t period = 0;
    int csc = 0;
    float cscBrightness = 0, cscContrast = 1.0;
    float cscSaturation = 1.0, cscHue = 0;
    VdpBitstreamBuffer bitstreamBuffer;
    VdpStatus vdp_st;
    VdpPictureInfoHEVC infoHEVC;
    VdpTime startTime;
    int8_t  target_index = -1;
    uint8_t use_vdpau = 1, use_x11 = 1, do_display = 1, step = 0;
    int32_t delay = 0;
    hevc_decoder_context context;
    uint32_t PicSizeInSamplesY;
    int32_t frames = -1, frame = 0;

    /* State variables. */
    /* TODO Move these to hevc_decoder_context structure? */
    GstH265Parser* parser = NULL;
    GstH265NalUnit* nalu = NULL;
    GstH265SliceHdr* slice = NULL;
    GstH265VPS* vps = NULL;
    GstH265SPS* sps = NULL;
    GstH265PPS* pps = NULL;
    GstH265SEIMessage* sei = NULL;

    /* TODO: Alternately parse these from the SPS. */
    vid_width=1920;
    vid_height=1080;

    memset(&infoHEVC, 0, sizeof(infoHEVC));
    memset(&context, 0, sizeof(context));

    /* Parse command line. */
    if(argc < 2)
    {
        PrintUsage();
        return -1;
    }
    for(i = 1; i < argc; i++)
    {
        if(!strcmp("-l", argv[i]))
        {
            loop = 1;
        }
        else if(!strcmp("-f", argv[i]))
        {
            if((i + 1) >= (argc - 1))
            {
                PrintUsage();
            }
            factor = atof(argv[i+1]);
            i++;
            if(factor > 0.0)         /* frames/sec */
            {
                factor = 1e9 / factor; /* nsec/frame */
                period = (uint64_t)factor;
            }
        }
        else if(!strcmp("-8", argv[i]))
        {
            bits_10 = 0;
        }
        else if(!strcmp("-10", argv[i]))
        {
            bits_10 = 1;
        }
        else if(!strcmp("-wins", argv[i]))
        {
            if((i + 1) >= (argc - 1))
            {
                PrintUsage();
            }
            num_win_ids = atoi(argv[i+1]);
            i++;
        }
        else if(!strcmp("-csc", argv[i]))
        {
            csc = 1;
        }
        else if(!strcmp("-cscb", argv[i]))
        {
            if((i + 1) >= (argc - 1))
            {
                PrintUsage();
            }
            cscBrightness = atof(argv[i+1]);
            i++;
        }
        else if(!strcmp("-cscc", argv[i]))
        {
            if((i + 1) >= (argc - 1))
            {
                PrintUsage();
            }
            cscContrast = atof(argv[i+1]);
            i++;
        }
        else if(!strcmp("-cscs", argv[i]))
        {
            if((i + 1) >= (argc - 1))
            {
                PrintUsage();
            }
            cscSaturation = atof(argv[i+1]);
            i++;
        }
        else if(!strcmp("-csch", argv[i]))
        {
            if((i + 1) >= (argc - 1))
            {
                PrintUsage();
            }
            cscHue = atof(argv[i+1]);
            i++;
        }
        /* Test mode, for non-VDPAU environments to check parsing and flow. */
        else if(!strcmp("-novdpau", argv[i]))
        {
            use_vdpau = 0;
            i++;
        }
        /* Test mode, for non-X11 environments to check parsing and flow. */
        /* Implies -novdpau */
        else if(!strcmp("-nox11", argv[i]))
        {
            use_x11 = 0;
            use_vdpau = 0;
            i++;
        }
        /* Step per frame. */
        else if(!strcmp("-step", argv[i]))
        {
            step = 1;
            i++;
        }
        /* No display, goes faster. */
        else if(!strcmp("-nodisplay", argv[i]))
        {
            do_display = 0;
            i++;
        }
        /* Number of milliseconds to wait between frames.
           Poor man's presentation queue timing management. */
        else if(!strcmp("-t", argv[i]))
        {
            if((i + 1) >= (argc - 1))
            {
                PrintUsage();
            }
            delay = atoi(argv[i+1]);
            i++;
        }
        /* Only decode this many frames. */
        else if(!strcmp("-frames", argv[i]))
        {
            if((i + 1) >= (argc - 1))
            {
                PrintUsage();
            }
            frames = atoi(argv[i+1]);
            i++;
        }
        /* TODO: Alternately parse these from the SPS. */
        else if(!strcmp("-x", argv[i]))
        {
            if((i + 1) >= (argc - 1))
            {
                PrintUsage();
            }
            vid_width = atof(argv[i+1]);
            i++;
        }
        else if(!strcmp("-y", argv[i]))
        {
            if((i + 1) >= (argc - 1))
            {
                PrintUsage();
            }
            vid_height = atof(argv[i+1]);
            i++;
        }
        else if(argv[i][0] == '-')
        {
            PrintUsage();
        }
    }

    /* Open file or die trying. */
    if(!(file = fopen(argv[argc - 1],"rb")))
    {
        printf("Input file %s not found\n",argv[1]);
        return -1;
    }

    /* Initialize GStreamer library for HEVC NAL Unit parsing. */
    parser = gst_h265_parser_new();
    if(!parser)
    {
        printf("Error: unable to call gst_h265_parser_new.\n");
        return -1;
    }

    if(allocate_gst_objects(&nalu, &slice, &vps, &sps, &pps, &sei) < 0)
    {
        printf("Failed to allocate Gst objects.\n");
        gst_h265_parser_free(parser);
        return -1;
    }

    /* Initialize X11. */

    if(use_x11)
    {
        win_x11_init_x11();
        for (i = 0; i < num_win_ids; i++)
        {
            win_x11_init_window(i);
        }
    }

    /* Initialize rendering. */

    /* We don't have the width or height here, we need to parse those from
       the SPS as pic_width_in_luma_samples/pic_height_in_luma_samples/
     */

    bitstreamBuffer.bitstream = calloc(NALU_BUFFER_LENGTH, sizeof(uint8_t));
    if(bitstreamBuffer.bitstream == NULL)
    {
        printf("Error: MALLOC: bitstreamBuffer.bitstream.\n");
        gst_h265_parser_free(parser);
        free_gst_objects(&nalu, &slice, &vps, &sps, &pps, &sei);
        return -1;
    }


    /*
       First, find the location whereby,
       "the next four bytes in the bitstream [are] 0x 00 00 00 01"
     */

START_OVER:

    /* rewind */
    rewind(file);

    context.IsFirstPicture = 1;

    /*

       The most interesting API usage is in this loop. The flow is:

       Parse the incoming bitstream.
       Pull out the next NAL unit.
       Parse every individual NAL unit.
       Update decoder state after each NAL unit, saving it to
       VdpPictureInfoHEVC.

       For VCL NAL units ("frames"), the player must handle some parts of
       Clause 8 as well as Annex C for correct decoding.

       The order of operations for decoding a VCL NAL unit is:

       8.2 NAL unit decoding process
       8.3.1 Decoding process for picture order count
       8.3.2 Decoding process for reference picture set
       C.3.2 Removal of pictures from the DPB
       8.3.3 Decoding process for generating unavailable reference pictures
       C.3.4 Current decoded picture marking and storage
       8.1 PicOutputFlag
       (8.3.4 through 8.7 - handled by VdpDecoderRender - see note below)
       C.3.3 Picture output

       This player does _not_ implement a coded picture buffer (CPB) as
       specified in C.2. We assume that a bitstream is encapsulated in a
       file that we can access as needed, and do not handle underflows or
       calculate timing.

       VdpDecoderRender models an instantaneous decoding process. A decoding
       process is defined in 8.1 as: NAL unit decoding (8.2), slice segment
       layer decoding (8.3), and decoding using all syntax elements (8.4, 8.5,
       8.6, 8.7). Since VDPAU is a NAL unit level API, any actions that are
       done per slice are handled by the implementation. This includes 8.3.4,
       8.4, 8.5, 8.6 and 8.7.

       This implementation uses VdpPictureInfoHEVC.RefPics[] as the decoded
       picture buffer (DPB). Other players are free to use RefPics[] directly,
       or to keep a local, separate DPB. Other implementations may also choose
       to maintain decoder state using a separate means, and copy data to
       VdpPictureInfoHEVC on the fly prior to calling VdpDecoderRender.

       For now, this player outputs frames in decode order, not display order.

     */

    /*
       Determine the start locations of NAL units, in chars past the
       beginning of the file.
     */
    while(get_next_nal_unit(file, bitstreamBuffer.bitstream, &nal_length)==0)
    {

        /* Got a NAL unit. Now parse it. */

        result = gst_h265_parser_identify_nalu(
                     parser,
                     (const guint8 *) bitstreamBuffer.bitstream,
                     0,
                     (gsize) nal_length,
                     nalu);

        if(check_nalu_result(result))
        {
            return -1;
        }
        else
        {
            printf("NAL decoded.\n");
            switch(nalu->type)
            {
                /* Video Coding Layer NAL Units */
            case GST_H265_NAL_SLICE_TRAIL_N:
            case GST_H265_NAL_SLICE_TRAIL_R:
            case GST_H265_NAL_SLICE_TSA_N:
            case GST_H265_NAL_SLICE_TSA_R:
            case GST_H265_NAL_SLICE_STSA_N:
            case GST_H265_NAL_SLICE_STSA_R:
            case GST_H265_NAL_SLICE_RADL_N:
            case GST_H265_NAL_SLICE_RADL_R:
            case GST_H265_NAL_SLICE_RASL_N:
            case GST_H265_NAL_SLICE_RASL_R:
            case GST_H265_NAL_SLICE_BLA_W_LP:
            case GST_H265_NAL_SLICE_BLA_W_RADL:
            case GST_H265_NAL_SLICE_BLA_N_LP:
            case GST_H265_NAL_SLICE_IDR_W_RADL:
            case GST_H265_NAL_SLICE_IDR_N_LP:
            case GST_H265_NAL_SLICE_CRA_NUT:
                printf("Video Coding Layer\n");

                /* Create VDPAU API objects: decoder, renderer. */

                if(use_vdpau && !context.vdpau_initialized)
                {
                    /*
                    TODO: Do this lazily. Only create objects once we have
                    parsed enough NAL units to know that we must perform
                    decoding.
                    */
                    CreateVdpapiObjects(&infoHEVC, &context, bits_10);
                    if (csc)
                    {
                        VdpCSCMatrix matrix;
                        VdpProcamp procamp =
                        {
                            VDP_PROCAMP_VERSION,
                            cscBrightness,
                            cscContrast,
                            cscSaturation,
                            cscHue
                        };
                        VdpVideoMixerAttribute attributes[] =
                        {
                            VDP_VIDEO_MIXER_ATTRIBUTE_CSC_MATRIX
                        };
                        const void *attribute_values[] = { &matrix };

                        vdp_st = vdp_generate_csc_matrix(
                                     /* inputs */
                                     &procamp, /* procamp */
                                     /* standard */
                                     VDP_COLOR_STANDARD_ITUR_BT_601,
                                     &matrix /* csc_matrix */
                                 );
                        CHECK_STATE

                        vdp_st = vdp_video_mixer_set_attribute_values(
                                     videoMixer, /* mixer */
                                     1, /* attribute_count */
                                     attributes, /* attributes */
                                     attribute_values /* attribute_values */
                                 );
                        CHECK_STATE
                    }
                    vdp_st = vdp_presentation_queue_get_time(
                                 vdp_flip_queue[0],
                                 &startTime
                             );
                    CHECK_STATE
                    context.vdpau_initialized = 1;
                }

                /* 8.2 NAL unit decoding process. */
                /* Populate GstH265SliceHdr... */
                gst_h265_parser_parse_slice_hdr(parser, nalu, slice);
                /* ...and propagate information to VdpPictureInfoHEVC. */
                update_picture_info_slice_header(
                    &infoHEVC, &context, slice, nalu, sps);
                nals++;
                /* 8.3.1 Decoding process for picture order count */
                decode_picture_order_count(&infoHEVC, &context, slice, nalu);
                /* 8.3.2 Decoding process for reference picture set */
                decode_reference_picture_set(&infoHEVC, &context, slice, sps);
                /* C.3.2 Removal of pictures from the DPB */
                remove_pictures_from_dpb(&infoHEVC, &context, slice, nalu);
                /* 8.3.3 Decoding process for generating unavailable reference
                   pictures */
                generate_unavailable_reference_pictures(
                    &infoHEVC, &context, nalu);
                /* C.3.4 Current decoded picture marking and storage. */
                target_index = get_decoded_picture_index(&context);
                if(target_index < 0)
                    printf("ERROR: Invalid target_index value\n");
                context.dpb_slice_pic_order_cnt_lsb[target_index] =
                    slice->pic_order_cnt_lsb;
                /* 8.1 PicOutputFlag */
                calculate_PicOutputFlag(&context, slice, nalu, target_index);
                /* Remainder of decoding process - 8.3.4 8.4 8.5 8.6 8.7 */
                bitstreamBuffer.struct_version = VDP_BITSTREAM_BUFFER_VERSION;

                /*
                   VDPAU HEVC NAL Length trickery.
                   NAL units of same type, layer id, and temporal id form same
                   picture. Need to find where the next differing NAL unit
                   begins in the bitstream to give the correct bitstream_bytes
                   value to VDPAU.
                 */

                while(peek_next_nal_unit(file) == 0)
                {
                    int nal_extra_length;
                    printf("Another NAL unit for this picture found!\n");
                    /* Truncate by 4 - don't repeat start codes */
                    get_next_nal_unit(file,
                                      (bitstreamBuffer.bitstream+nal_length-4),
                                      &nal_extra_length);
                    nal_length += nal_extra_length - 4;
                }

                printf("Decoding a buffer of length %d\n", nal_length);
                bitstreamBuffer.bitstream_bytes = nal_length;
                if(use_vdpau)
                {
                    vdp_st = vdp_decoder_render(
                                 decoder,
                                 context.scratch_frames[target_index],
                                 (void*)&infoHEVC,
                                 1,
                                 &bitstreamBuffer
                             );
                    CHECK_STATE
                }
                /* TODO - I think these need to be done AFTER decoding? */
                infoHEVC.PicOrderCntVal[target_index] =
                    infoHEVC.CurrPicOrderCntVal;
                infoHEVC.RefPics[target_index] =
                    context.scratch_frames[target_index];
                /* C.3.3 Frame Output */
                if(use_vdpau && do_display)
                {
                    DisplayFrame(&infoHEVC, period, target_index);
                }
                context.IsFirstPicture = 0;
                if(delay)
                    usleep(delay);
                else if (step)
                {
                    printf("Press 'q' to quit, <any key> for next frame.\n");
                    if(getchar() == 'q') return -1;
                }
                frame++;
                if(frames > 0 && frame > frames)
                    return 0;
                break;
                /* Video Parameter Set */
            case GST_H265_NAL_VPS:
                printf("Video Parameter Set\n");
                /* Populate GstH265VPS */
                gst_h265_parser_parse_vps(
                    parser,
                    nalu,
                    vps);
                update_picture_info_vps(&infoHEVC, vps);
                nals++;
                break;
                /* Sequence Parameter Set */
            case GST_H265_NAL_SPS:
                printf("Sequence Parameter Set\n");
                /* Populate GstH265SPS */
                gst_h265_parser_parse_sps(
                    parser,
                    nalu,
                    sps,
                    (gboolean) TRUE);
                update_picture_info_sps(&infoHEVC, sps);
                nals++;
                /* A.4.1 General tier and level limits. Calculate MaxDpbSize.*/
                /* TODO - Make this more general. This is written against the
                   NVIDIA VDPAU implementation which supports Tier 5.1. */
                /* TODO - Move this into update_picture_info_sps ? */
                PicSizeInSamplesY = sps->pic_width_in_luma_samples
                                    * sps->pic_height_in_luma_samples;
                if(sps->pic_width_in_luma_samples > SQRT_MAX_LUMA_PS_X8 ||
                        sps->pic_height_in_luma_samples > SQRT_MAX_LUMA_PS_X8)
                    printf("ERROR: picture width/height is out of bounds.\n");

                if(PicSizeInSamplesY <= (MAX_LUMA_PS >> 2))
                    context.MaxDpbSize = min(4*MAX_DPB_PIC_BUF, 16);
                else if(PicSizeInSamplesY <= (MAX_LUMA_PS >> 1))
                    context.MaxDpbSize = min(2*MAX_DPB_PIC_BUF, 16);
                else if(PicSizeInSamplesY <= ((3*MAX_LUMA_PS)>>2))
                    context.MaxDpbSize = min((4*MAX_DPB_PIC_BUF)/3, 16);
                else
                    context.MaxDpbSize = MAX_DPB_PIC_BUF;

                break;
                /* Picture Parameter Set */
            case GST_H265_NAL_PPS:
                printf("Picture Parameter Set\n");
                /* Populate GstH265PPS */
                gst_h265_parser_parse_pps(
                    parser,
                    nalu,
                    pps);
                update_picture_info_pps(&infoHEVC, pps);
                nals++;
                break;
                /* Supplemental Enhancement Information */
            case GST_H265_NAL_PREFIX_SEI:
            case GST_H265_NAL_SUFFIX_SEI:
                printf("Supplemental Enhancement Information\n");
                /* Populate GstH265SEIMessage */
                gst_h265_parser_parse_sei(
                    parser,
                    nalu,
                    sei);
                update_picture_info_sei(&infoHEVC, sei);
                nals++;
                break;
            case GST_H265_NAL_EOS:
                context.IsFirstPicture = 1;
                nals++;
                break;
                /* All others. */
            default:
                printf("Uknown NAL Unit type...\n");
                gst_h265_parser_parse_nal(parser, nalu);
                break;
            }
        }
    }

    printf("Found %d NAL units!\n", nals);

    printf("%s\n", "Parsing complete.");

    /* clear out display Queue */
    /* TODO - Now broken now that DisplayFrame takes a target_index. Fix! */
    if(use_vdpau && do_display)
    {
        for(i = 0; i < NUM_OUTPUT_SURFACES; i++)
        {
            if(displayQueue[1] != -1)
            {
                DisplayFrame(&infoHEVC, period, 0);
            }
            MoveQueue();
        }
    }

    if(loop)
    {
        /* xkcd.com/292 */
        goto START_OVER;
    }

    if(use_vdpau)
    {
        DestroyVdpapiObjects(&infoHEVC, &context);
    }

    if(use_x11)
    {
        for (i = 0; i < num_win_ids; i++)
        {
            win_x11_fini_window(i);
        }
        win_x11_fini_x11();
    }

    free_gst_objects(&nalu, &slice, &vps, &sps, &pps, &sei);
    gst_h265_parser_free(parser);
    free((void *)bitstreamBuffer.bitstream);

    fclose(file);

    return 0;
}
