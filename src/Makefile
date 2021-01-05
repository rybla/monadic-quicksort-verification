SOURCE_DIRECTORY=~/Repositories/oopsla2020-artifact/liquid-benchmark/liquid-base/liquid-base/src
SOURCE_FILES=$(shell find . -name "*.hs")
LIQUID_OPTIONS=--reflection --ple --typed-holes --extensionality --higherorder --notermination --diff --prune-unsorted
GHC_OPTIONS=--ghc-option=-XExplicitForAll --ghc-option=-XRankNTypes --ghc-option=--XScopedTypeVariables

check:
	liquid -i ${SOURCE_DIRECTORY} ${SOURCE_FILES} ${LIQUID_OPTIONS} ${GHC_OPTIONS}
