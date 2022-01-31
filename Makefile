
IDRIS := idris2

PACKAGE = fvect.ipkg

all: build

.PHONY: build

build:
	$(IDRIS) --build $(PACKAGE)

.PHONY: clean

clean:
	$(IDRIS) --clean $(PACKAGE)

.PHONY: install

install:
	$(IDRIS) --install $(PACKAGE)
	
install-with-src:
	$(IDRIS) --install-with-src $(PACKAGE)
