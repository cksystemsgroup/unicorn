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
BTORS := $(patsubst %.c,%.btor2,$(SRCS))
CNFS := $(patsubst %.c,%.cnf,$(SRCS))
DATAS := $(patsubst %.c,%.data,$(SRCS))

.PHONY: all clean obj bytecode btor2 cnf c2 cnf2

all: data.csv
	@column -s, -t $<

clean:
	rm -f data.csv
	rm -f $(OBJS)
	rm -f $(GCCS)
	rm -f $(BCS)
	rm -f $(BTORS)
	rm -f $(CNFS)
	rm -f $(DATAS)
	rm -f klee-last
	rm -rf klee-out-*

obj: $(OBJS)
gcc: $(GCCS)
bytecode: $(BCS)
btor2: $(BTORS)
cnf: $(CNFS)

data.csv: $(DATAS) 
	@echo "name,#unroll,#sat,btormc,unicorn+boolector-all,unicorn+boolector-r,unicorn+boolector-1,unicorn+z3-all,unicorn+z3-r,unicorn+z3-1,unicorn+kissat-all,unicorn+kissat-r,unicorn+kissat-1,unicorn+cadical-all,unicorn+cadical-r,unicorn+cadical-1,klee" > $@
	@for f in $^; do \
	  echo -n $$(grep -oP 'name : \K\S+' $$f),                          >> $@; \
	  echo -n $$(grep -oP 'unroll : \K\S+' $$f),                        >> $@; \
	  echo -n $$(grep -oP 'solutions : \K\S+' $$f),                     >> $@; \
	  echo -n $$(grep -oP 'btormc-time : \K\S+' $$f),                   >> $@; \
	  echo -n $$(grep -oP 'unicorn-boolector-time-all : \K\S+' $$f),    >> $@; \
	  echo -n $$(grep -oP 'unicorn-boolector-time-reverse : \K\S+' $$f),>> $@; \
	  echo -n $$(grep -oP 'unicorn-boolector-time-1 : \K\S+' $$f),		>> $@; \
	  echo -n $$(grep -oP 'unicorn-z3-time-all : \K\S+' $$f),           >> $@; \
	  echo -n $$(grep -oP 'unicorn-z3-time-reverse : \K\S+' $$f),       >> $@; \
	  echo -n $$(grep -oP 'unicorn-z3-time-1 : \K\S+' $$f),       		>> $@; \
	  echo -n $$(grep -oP 'unicorn-kissat-time-all : \K\S+' $$f),       >> $@; \
	  echo -n $$(grep -oP 'unicorn-kissat-time-reverse : \K\S+' $$f),   >> $@; \
	  echo -n $$(grep -oP 'unicorn-kissat-time-1 : \K\S+' $$f),   		>> $@; \
	  echo -n $$(grep -oP 'unicorn-cadical-time-all : \K\S+' $$f),      >> $@; \
	  echo -n $$(grep -oP 'unicorn-cadical-time-reverse : \K\S+' $$f),  >> $@; \
	  echo -n $$(grep -oP 'unicorn-cadical-time-1 : \K\S+' $$f),  		>> $@; \
	  echo -n $$(grep -oP 'klee-time : \K\S+' $$f),                     >> $@; \
	  echo >> $@; \
	done

%.m: %.c
	$(SELFIE) -c ../tools/cstar-lib.c $< -o $@ > /dev/null

%.n: %.c
	$(RVGCC) -Wno-div-by-zero -include ../tools/cstar-gcc.h $< -o $@

%.bc: %.c
	clang -Werror -Wno-main-return-type -Wno-return-type -O0 \
	      -Xclang -disable-O0-optnone -include ../tools/cstar-klee.h\
	      -emit-llvm -c $< -o $@

# Generates a non-unrolled non-optimized BTOR2 file.
%.btor2: %.m
	$(UNICORN) beator $< -o $@

# Generates an unrolled constant-folded bit-blasted CNF file.
%.cnf: %.m
	$(eval UNROLL := $(shell grep -oP '// @UNROLL = \K\d+' $*.c))
	$(UNICORN) beator $< -o $@ -u $(UNROLL) -p -b -d --discretize-memory

%.data: %.btor2 %.m %.bc %.c2 %.cnf 
	$(eval UNROLL := $(shell grep -oP '// @UNROLL = \K\d+' $*.c))
	$(eval SOLUTIONS := $(shell grep -oP '// @SOLUTIONS = \K\d+' $*.c))
	@echo name : $* > $@
	@echo unroll : $(UNROLL) >> $@
	@echo solutions : $(SOLUTIONS) >> $@
	@echo -n "btormc-time : " >> $@
	timeout 5m bash $(MYTIME) $(BTORMC) -kmax $(UNROLL) $*.btor2 >> $@ || echo T >> $@

	@echo -n "unicorn-boolector-time-all : " >> $@
	timeout 5m bash $(MYTIME) $(UNICORN) beator $*.m -u $(UNROLL) -p -s boolector --fast-minimize >> $@ || echo T >> $@
	@echo -n "unicorn-boolector-time-reverse : " >> $@
	timeout 5m bash $(MYTIME) $(UNICORN) beator $*.m -u $(UNROLL) -p -s boolector --fast-minimize --terminate-on-bad >> $@ || echo T >> $@
	timeout 5m bash $(MYTIME) $(UNICORN) beator $*.m -u $(UNROLL) -p -s boolector --fast-minimize --one-query >> $@ || echo T >> $@

	@echo -n "unicorn-z3-time-all : " >> $@ 
	timeout 5m bash $(MYTIME) $(UNICORN) beator $*.m -u $(UNROLL) -p -s z3 --fast-minimize >> $@ || echo T >> $@
	@echo -n "unicorn-z3-time-reverse : " >> $@ 
	timeout 5m bash $(MYTIME) $(UNICORN) beator $*.m -u $(UNROLL) -p -s z3 --fast-minimize --terminate-on-bad >> $@ || echo T >> $@
	@echo -n "unicorn-z3-time-1 : " >> $@ 
	timeout 5m bash $(MYTIME) $(UNICORN) beator $*.m -u $(UNROLL) -p -s z3 --fast-minimize --one-query >> $@ || echo T >> $@

	@echo -n "unicorn-kissat-time-all : " >> $@
	timeout 5m bash $(MYTIME) $(UNICORN) beator $*.m -u $(UNROLL) -p --sat-solver kissat --discretize-memory >> $@ || echo T >> $@
	@echo -n "unicorn-kissat-time-reverse : " >> $@
	timeout 5m bash $(MYTIME) $(UNICORN) beator $*.m -u $(UNROLL) -p --sat-solver kissat --discretize-memory --terminate-on-bad >> $@ || echo T >> $@
	@echo -n "unicorn-kissat-time-1 : " >> $@
	timeout 5m bash $(MYTIME) $(UNICORN) beator $*.m -u $(UNROLL) -p --sat-solver kissat --discretize-memory --one-query >> $@ || echo T >> $@

	@echo -n "unicorn-cadical-time-all : " >> $@
	timeout 5m bash $(MYTIME) $(UNICORN) beator $*.m -u $(UNROLL) -p --sat-solver cadical --discretize-memory >> $@ || echo T >> $@
	@echo -n "unicorn-cadical-time-reverse : " >> $@
	timeout 5m bash $(MYTIME) $(UNICORN) beator $*.m -u $(UNROLL) -p --sat-solver cadical --discretize-memory --terminate-on-bad >> $@ || echo T >> $@
	@echo -n "unicorn-cadical-time-1 : " >> $@
	timeout 5m bash $(MYTIME) $(UNICORN) beator $*.m -u $(UNROLL) -p --sat-solver cadical --discretize-memory --one-query >> $@ || echo T >> $@

	@echo -n "klee-time : " >> $@
	timeout 5m bash $(MYTIME) $(KLEE) $*.bc >> $@ || echo T >> $@
