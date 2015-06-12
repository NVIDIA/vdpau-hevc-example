# Copyright (c) 2015, NVIDIA CORPORATION.  All rights reserved.
#
# This library is free software; you can redistribute it and/or
# modify it under the terms of the GNU Lesser General Public
# License, version 2.1, as published by the Free Software Foundation.
#
# This library is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
# Lesser General Public License for more details.
#
# You should have received a copy of the GNU Lesser General Public
# License along with this program.  If not, see
# <http://www.gnu.org/licenses/>.

# parser: a simple HEVC elementary stream parser wrapper
CC = gcc

CFLAGS = \
    -DGST_USE_UNSTABLE_API \
    -Wall \
    -Werror \
    -O0 \
    -ggdb

INCLUDES = \
     -I /usr/include/gstreamer-0.10 \
     $(shell pkg-config --cflags glib-2.0) \
     -I /usr/include/libxml2 \
     -I vdpau-win-x11 \
     -I /usr/include/X11

LFLAGS =

LIBS = \
    -lm \
     $(shell pkg-config --libs glib-2.0) \
    -lvdpau \
    -lX11

SRCS = \
    nalutils.c \
    gstbitreader.c \
    gstbytereader.c \
    gsth265parser.c \
    vdpau-win-x11/win_x11.c \
    main.c

OBJS = $(SRCS:.c=.o)

MAIN = vdpau_hw_hevc

.PHONY: depend clean

all:    $(MAIN)
	@echo  parser compiled.

$(MAIN): $(OBJS)
	$(CC) $(CFLAGS) $(INCLUDES) -o $(MAIN) $(OBJS) $(LFLAGS) $(LIBS)

.c.o:
	$(CC) $(CFLAGS) $(INCLUDES) -c $<  -o $@

clean:
	$(RM) *.o *~ $(MAIN)

depend: $(SRCS)
	makedepend $(INCLUDES) $^

# DO NOT DELETE THIS LINE -- make depend needs it

