FIGURE := figure
DPI    ?= 300

.PHONY: build clean

build: $(FIGURE).png

# figure.typ plots results.json, so a fresh benchmark run redraws the figure.
$(FIGURE).png: $(FIGURE).typ results.json
	typst compile --format png --ppi $(DPI) $< $@

clean:
	rm -f $(FIGURE).png
