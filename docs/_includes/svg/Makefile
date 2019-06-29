#===============================================================================
# Makefile
#===============================================================================

DEST_DIR=../../assets/images
OUTPUTS=factorizer canonizer store share portfolio pipeline work-in-progress

#-------------------------------------------------------------------------------

SOUTPUTS := $(OUTPUTS:%=%.svg)
POUTPUTS := $(OUTPUTS:%=$(DEST_DIR)/%.png)

#-------------------------------------------------------------------------------

all: $(POUTPUTS) svgs.svg

$(DEST_DIR)/%.png: %.svg
	convert $< $@

%.svg: svgs.txt svgs.awk
	gawk -v picture=$(patsubst %.svg,%,$@) -f svgs.awk < svgs.txt > $@

svgs.svg: svgs.txt svgs.awk
	gawk -f svgs.awk < svgs.txt > $@
