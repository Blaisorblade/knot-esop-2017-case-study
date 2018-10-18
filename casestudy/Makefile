SUBDIRS := ${shell find . \( ! -name . -prune ! -name .git -prune \) -type d -print}

default: all
all clean depend : $(SUBDIRS)

# Hacky way of using a double colon rule to call make on the subdirectories using
# the same target that make on this file was called with. Together with the
# above that allows building / cleaning in parallel.
# Also see https://www.gnu.org/software/make/manual/html_node/Double_002dColon.html
$(SUBDIRS)::
	$(MAKE) -C $@ $(MAKECMDGOALS)

.PHONY: all clean depend $(SUBDIRS)
