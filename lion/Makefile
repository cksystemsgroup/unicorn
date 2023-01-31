SELFIE = selfie
RVGCC = riscv64-unknown-elf-gcc
UNICORN = ../target/release/unicorn
MYTIME = ../tools/mytime.sh
MINISAT = minisat
BTORMC = btormc
KLEE = klee

SRCS := $(wildcard *.c)
OBJS := $(patsubst %.c,%.m,$(SRCS))
GCCS := $(patsubst %.c,%.n,$(SRCS))
BCS := $(patsubst %.c,%.bc,$(SRCS))
BMCS := $(patsubst %.c,%.bmc,$(SRCS))
BTORS := $(patsubst %.c,%.btor2,$(SRCS))
CNFS := $(patsubst %.c,%.cnf,$(SRCS))
DATAS := $(patsubst %.c,%.data,$(SRCS))

.PHONY: all clean obj gcc bytecode btor2 btormc cnf tex

all: data.csv
	@column -s, -t $<

clean:
	rm -f data.csv
	rm -f $(OBJS)
	#rm -f $(GCCS)
	rm -f $(BCS)
	rm -f $(BMCS)
	rm -f $(BTORS)
	rm -f $(CNFS)
	rm -f $(DATAS)
	rm -f klee-last
	rm -rf klee-out-*

obj: $(OBJS)
gcc: $(GCCS)
bytecode: $(BCS)
btor2: $(BTORS)
btormc: $(BMCS)
cnf: $(CNFS)

tex: data.csv
	@column -o'& ' -s, -t $< | sed 's|& $$|\\\\|'

data.csv: $(DATAS) 
	@echo "name,#unroll,#sat,btormc,unicorn+boolector-all,unicorn+boolector-r,unicorn+boolector-1,unicorn+z3-all,unicorn+z3-r,unicorn+z3-1,unicorn+kissat-all,unicorn+kissat-r,unicorn+kissat-1,unicorn+cadical-all,unicorn+cadical-r,unicorn+cadical-1,minisat,klee" > $@
	@for f in $^; do \
	  echo -n $$(grep -oP '^name : \K.+' $$f),                          >> $@; \
	  echo -n $$(grep -oP 'unroll : \K\S+' $$f),                        >> $@; \
	  echo -n $$(grep -oP 'solutions : \K\S+' $$f),                     >> $@; \
	  echo -n $$(grep -oP 'btormc-time : \K\S+' $$f),                   >> $@; \
	  echo -n $$(grep -oP 'unicorn-boolector-time-all : \K\S+' $$f),    >> $@; \
	  echo -n $$(grep -oP 'unicorn-boolector-time-reverse : \K\S+' $$f),>> $@; \
	  echo -n $$(grep -oP 'unicorn-boolector-time-1 : \K\S+' $$f),      >> $@; \
	  echo -n $$(grep -oP 'unicorn-z3-time-all : \K\S+' $$f),           >> $@; \
	  echo -n $$(grep -oP 'unicorn-z3-time-reverse : \K\S+' $$f),       >> $@; \
	  echo -n $$(grep -oP 'unicorn-z3-time-1 : \K\S+' $$f),             >> $@; \
	  echo -n $$(grep -oP 'unicorn-kissat-time-all : \K\S+' $$f),       >> $@; \
	  echo -n $$(grep -oP 'unicorn-kissat-time-reverse : \K\S+' $$f),   >> $@; \
	  echo -n $$(grep -oP 'unicorn-kissat-time-1 : \K\S+' $$f),         >> $@; \
	  echo -n $$(grep -oP 'unicorn-cadical-time-all : \K\S+' $$f),      >> $@; \
	  echo -n $$(grep -oP 'unicorn-cadical-time-reverse : \K\S+' $$f),  >> $@; \
	  echo -n $$(grep -oP 'unicorn-cadical-time-1 : \K\S+' $$f),        >> $@; \
	  echo -n $$(printf '%.4f' `grep -oP 'CPU time\s+: \K\S+' $$f`),    >> $@; \
	  echo -n $$(grep -oP 'klee-time : \K\S+' $$f),                     >> $@; \
	  echo >> $@; \
	done

%.m: %.c ../tools/cstar-lib.c
	$(SELFIE) -c ../tools/cstar-lib.c $< -o $@ > /dev/null

%.n: %.c ../tools/cstar-gcc.h
	$(RVGCC) -Wno-div-by-zero -include ../tools/cstar-gcc.h $< -o $@

%.bc: %.c ../tools/cstar-klee.h
	clang -Werror -Wno-main-return-type -Wno-return-type -O0 \
	      -Xclang -disable-O0-optnone -include ../tools/cstar-klee.h \
	      -emit-llvm -c $< -o $@

# Generates a non-unrolled non-optimized BTOR2 file.
%.btor2: %.n
	$(eval FLAGS := $(shell grep -oP '// @FLAGS = \K.+' $*.c))
	$(UNICORN) beator $< -o $@ $(FLAGS)

# Generates a model-checking result using BtorMC (for debugging).
%.bmc: %.btor2
	$(eval UNROLL := $(shell grep -oP '// @UNROLL = \K\d+' $*.c))
	grep bad $< | nl -v0 | sed 's|^|//|' > $@
	$(BTORMC) -kmax $(UNROLL) $< >> $@

# Generates an unrolled constant-folded bit-blasted CNF file.
%.cnf: %.n
	$(eval UNROLL := $(shell grep -oP '// @UNROLL = \K\d+' $*.c))
	$(eval FLAGS := $(shell grep -oP '// @FLAGS = \K.+' $*.c))
	$(UNICORN) beator $< -o $@ $(FLAGS) -u $(UNROLL) -p -b -d

%.data: %.btor2 %.n %.cnf %.bc
	$(eval UNROLL := $(shell grep -oP '// @UNROLL = \K\d+' $*.c))
	$(eval FLAGS := $(shell grep -oP '// @FLAGS = \K.+' $*.c))
	$(eval SOLUTIONS := $(shell grep -oP '// @SOLUTIONS = \K\d+' $*.c))
	$(eval NAME := $(shell grep -oP '// @NAME = \K.+' $*.c))
	@echo filename : $* > $@
	@echo "name : $(NAME)" >> $@
	@echo unroll : $(UNROLL) >> $@
	@echo solutions : $(SOLUTIONS) >> $@
	@echo -n "btormc-time : " >> $@
	timeout 5m bash $(MYTIME) $(BTORMC) -kmax $(UNROLL) $*.btor2 >> $@ || echo T >> $@

	@echo -n "unicorn-boolector-time-all : " >> $@
	timeout 1m bash $(MYTIME) $(UNICORN) beator $*.n $(FLAGS) -u $(UNROLL) -p -s boolector --discretize-memory --fast-minimize >> $@ || echo T >> $@
	@echo -n "unicorn-boolector-time-reverse : " >> $@
	timeout 1m bash $(MYTIME) $(UNICORN) beator $*.n $(FLAGS) -u $(UNROLL) -p -s boolector --discretize-memory --fast-minimize --terminate-on-bad >> $@ || echo T >> $@
	@echo -n "unicorn-boolector-time-1 : " >> $@
	timeout 1m bash $(MYTIME) $(UNICORN) beator $*.n $(FLAGS) -u $(UNROLL) -p -s boolector --discretize-memory --fast-minimize --one-query >> $@ || echo T >> $@

	@echo -n "unicorn-z3-time-all : " >> $@ 
	timeout 1m bash $(MYTIME) $(UNICORN) beator $*.n $(FLAGS) -u $(UNROLL) -p -s z3 --discretize-memory --fast-minimize >> $@ || echo T >> $@
	@echo -n "unicorn-z3-time-reverse : " >> $@ 
	timeout 1m bash $(MYTIME) $(UNICORN) beator $*.n $(FLAGS) -u $(UNROLL) -p -s z3 --discretize-memory --fast-minimize --terminate-on-bad >> $@ || echo T >> $@
	@echo -n "unicorn-z3-time-1 : " >> $@ 
	timeout 1m bash $(MYTIME) $(UNICORN) beator $*.n $(FLAGS) -u $(UNROLL) -p -s z3 --discretize-memory --fast-minimize --one-query >> $@ || echo T >> $@

	@echo -n "unicorn-kissat-time-all : " >> $@
	timeout 1m bash $(MYTIME) $(UNICORN) beator $*.n $(FLAGS) -u $(UNROLL) -p --sat-solver kissat >> $@ || echo T >> $@
	@echo -n "unicorn-kissat-time-reverse : " >> $@
	timeout 1m bash $(MYTIME) $(UNICORN) beator $*.n $(FLAGS) -u $(UNROLL) -p --sat-solver kissat --terminate-on-bad >> $@ || echo T >> $@
	@echo -n "unicorn-kissat-time-1 : " >> $@
	timeout 1m bash $(MYTIME) $(UNICORN) beator $*.n $(FLAGS) -u $(UNROLL) -p --sat-solver kissat --one-query >> $@ || echo T >> $@

	@echo -n "unicorn-cadical-time-all : " >> $@
	timeout 1m bash $(MYTIME) $(UNICORN) beator $*.n $(FLAGS) -u $(UNROLL) -p --sat-solver cadical >> $@ || echo T >> $@
	@echo -n "unicorn-cadical-time-reverse : " >> $@
	timeout 1m bash $(MYTIME) $(UNICORN) beator $*.n $(FLAGS) -u $(UNROLL) -p --sat-solver cadical --terminate-on-bad >> $@ || echo T >> $@
	@echo -n "unicorn-cadical-time-1 : " >> $@
	timeout 1m bash $(MYTIME) $(UNICORN) beator $*.n $(FLAGS) -u $(UNROLL) -p --sat-solver cadical --one-query >> $@ || echo T >> $@

	@echo -n "klee-time : " >> $@
	timeout 5m bash $(MYTIME) $(KLEE) $*.bc >> $@ || echo T >> $@

	@echo "minisat-output ..." >> $@
	$(MINISAT) $*.cnf | tee -a $@
