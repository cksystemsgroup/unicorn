SELFIE = selfie
UNICORN = ../target/release/unicorn
MYTIME = ../tools/mytime.sh
MINISAT = minisat
BTORMC = btormc
KLEE = klee

SRCS := $(wildcard *.c)
OBJS := $(patsubst %.c,%.m,$(SRCS))
BCS := $(patsubst %.c,%.bc,$(SRCS))
BTORS := $(patsubst %.c,%.btor2,$(SRCS))
CNFS := $(patsubst %.c,%.cnf,$(SRCS))
DATAS := $(patsubst %.c,%.data,$(SRCS))

.PHONY: all clean obj bytecode btor2 cnf

all: data.csv
	@column -s, -t $<

clean:
	rm -f data.csv
	rm -f $(OBJS)
	rm -f $(BCS)
	rm -f $(BTORS)
	rm -f $(CNFS)
	rm -f $(DATAS)
	rm -f klee-last
	rm -rf klee-out-*

obj: $(OBJS)
bytecode: $(BCS)
btor2: $(BTORS)
cnf: $(CNFS)

data.csv: $(DATAS)
	@echo "name,#unroll,#sat,btormc,unicorn+boolector,unicorn+z3,unicorn+kissat,unicorn+cadical,klee" > $@
	@for f in $^; do \
	  echo -n $$(grep -oP 'name : \K\S+' $$f),                          >> $@; \
	  echo -n $$(grep -oP 'unroll : \K\S+' $$f),                        >> $@; \
	  echo -n $$(grep -oP 'solutions : \K\S+' $$f),                     >> $@; \
	  echo -n $$(grep -oP 'btormc-time : \K\S+' $$f),                   >> $@; \
	  echo -n $$(grep -oP 'unicorn-boolector-time : \K\S+' $$f),        >> $@; \
	  echo -n $$(grep -oP 'unicorn-z3-time : \K\S+' $$f),               >> $@; \
	  echo -n $$(grep -oP 'unicorn-kissat-time : \K\S+' $$f),           >> $@; \
	  echo -n $$(grep -oP 'unicorn-cadical-time : \K\S+' $$f),          >> $@; \
	  echo -n $$(grep -oP 'klee-time : \K\S+' $$f),                     >> $@; \
	  echo >> $@; \
	done

%.m: %.c
	$(SELFIE) -c ../tools/cstar-lib.c $< -o $@ > /dev/null

%.bc: %.c
	clang -Werror -Wno-main-return-type -Wno-return-type -O0 \
	      -Xclang -disable-O0-optnone -include ../tools/cstar-klee.h \
	      -emit-llvm -c $< -o $@

# Generates a non-unrolled non-optimized BTOR2 file.
%.btor2: %.m
	$(UNICORN) beator $< -o $@

# Generates an unrolled constant-folded bit-blasted CNF file.
%.cnf: %.m
	$(eval UNROLL := $(shell grep -oP '// @UNROLL = \K\d+' $*.c))
	$(UNICORN) beator $< -o $@ -u $(UNROLL) -p -b -d

%.data: %.btor2 %.m %.bc
	$(eval UNROLL := $(shell grep -oP '// @UNROLL = \K\d+' $*.c))
	$(eval SOLUTIONS := $(shell grep -oP '// @SOLUTIONS = \K\d+' $*.c))
	@echo name : $* > $@
	@echo unroll : $(UNROLL) >> $@
	@echo solutions : $(SOLUTIONS) >> $@
	@echo -n "btormc-time : " >> $@
	$(MYTIME) $(BTORMC) -kmax $(UNROLL) $*.btor2 >> $@
	@echo -n "unicorn-boolector-time : " >> $@
	$(MYTIME) $(UNICORN) beator $*.m -u $(UNROLL) -p -s boolector --fast-minimize >> $@
	@echo -n "unicorn-z3-time : " >> $@
	$(MYTIME) $(UNICORN) beator $*.m -u $(UNROLL) -p -s z3 --fast-minimize >> $@
	@echo -n "unicorn-kissat-time : " >> $@
	$(MYTIME) $(UNICORN) beator $*.m -u $(UNROLL) -p --sat-solver kissat --discretize-memory >> $@
	@echo -n "unicorn-cadical-time : " >> $@
	$(MYTIME) $(UNICORN) beator $*.m -u $(UNROLL) -p --sat-solver cadical --discretize-memory >> $@
	@echo -n "klee-time : " >> $@
	$(MYTIME) $(KLEE) $*.bc >> $@
	#$(MINISAT) $*.cnf | tee -a $@
