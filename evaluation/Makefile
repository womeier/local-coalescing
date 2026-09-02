FIGURE := figure
DPI    ?= 300

.PHONY: build clean

build: $(FIGURE).png

$(FIGURE).png: $(FIGURE).typ
	typst compile --format png --ppi $(DPI) $< $@

clean:
	rm -f $(FIGURE).png
