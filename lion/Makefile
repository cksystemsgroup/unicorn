SELFIE = selfie
UNICORN = ../target/release/unicorn
MYTIME = ../tools/mytime.sh
MINISAT = minisat
BTORMC = btormc
KLEE = klee
CBMC = cbmc

SRCS := $(wildcard *.c)
SRCS2 := $(wildcard cbmc_srcs/*.c) # CBMC srcs
OBJS := $(patsubst %.c,%.m,$(SRCS))
BCS := $(patsubst %.c,%.bc,$(SRCS))
BTORS := $(patsubst %.c,%.btor2,$(SRCS))
CNFS := $(patsubst %.c,%.cnf,$(SRCS))
CNFS2 := $(patsubst %.c,%.cnf2,$(SRCS)) # CBMC cnfs
DATAS := $(patsubst %.c,%.data,$(SRCS))

.PHONY: all clean obj bytecode btor2 cnf c2 cnf2

all: data.csv
	@column -s, -t $<

clean:
	rm -f data.csv
	rm -f $(OBJS)
	rm -f $(BCS)
	rm -f $(BTORS)
	rm -f $(CNFS)
	rm -f $(CNFS2)
	rm -f $(DATAS)
	rm -f klee-last
	rm -rf klee-out-*

obj: $(OBJS)
bytecode: $(BCS)
btor2: $(BTORS)
cnf: $(CNFS)
cnf2: $(CNFS2)
c2: $(SRCS2)

data.csv: $(DATAS) 
	@echo "name,#unroll,#sat,btormc,unicorn+boolector,unicorn+z3,unicorn+kissat,unicorn+cadical,klee,unicorn+minisat,cbmc+minisat,unicorn-vars,unicorn-clauses,cbmc-vars,cbmc-clauses" > $@
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
	  echo -n $$(grep -oP 'minisat-unicorn : \K\S+' $$f),               >> $@; \
	  echo -n $$(grep -oP 'minisat-cbmc : \K\S+' $$f),                  >> $@; \
	  echo -n $$(grep -oP 'unicorn-vars : \K\S+' $$f),              	>> $@; \
	  echo -n $$(grep -oP 'unicorn-clauses : \K\S+' $$f),           	>> $@; \
	  echo -n $$(grep -oP 'cbmc-vars : \K\S+' $$f),              		>> $@; \
	  echo -n $$(grep -oP 'cbmc-clauses : \K\S+' $$f),           		>> $@; \
	  echo >> $@; \
	done




%.m: %.c
	$(SELFIE) -c ../tools/cstar-lib.c $< -o $@ > /dev/null

%.bc: %.c
	clang -Werror -Wno-main-return-type -Wno-return-type -O0 \
	      -Xclang -disable-O0-optnone -include ../tools/cstar-klee.h\
	      -emit-llvm -c $< -o $@

%.c2: %.c
	if [ ! -d "cbmc_srcs" ]; then mkdir cbmc_srcs; fi
	@cat ../tools/cstar-cbmc.h > cbmc_srcs/$<
	@cat $< >> cbmc_srcs/$<

# Generates a non-unrolled non-optimized BTOR2 file.
%.btor2: %.m
	$(UNICORN) beator $< -o $@

# Generates an unrolled constant-folded bit-blasted CNF file.
%.cnf: %.m
	$(eval UNROLL := $(shell grep -oP '// @UNROLL = \K\d+' $*.c))
	$(UNICORN) beator $< -o $@ -u $(UNROLL) -p -b -d --discretize-memory

# Generates the a CNF file with CBMC.
%.cnf2: %.c
	$(eval UNROLL := $(shell grep -oP '// @UNROLL = \K\d+' $*.c))
	$(CBMC) cbmc_srcs/$< --outfile $@ --depth $(UNROLL) --slice-formula --bounds-check --pointer-check --div-by-zero-check --dimacs

%.data: %.btor2 %.m %.bc %.c2 %.cnf %.cnf2
	$(eval UNROLL := $(shell grep -oP '// @UNROLL = \K\d+' $*.c))
	$(eval SOLUTIONS := $(shell grep -oP '// @SOLUTIONS = \K\d+' $*.c))
	$(eval UNICORNVARS := $(shell grep -oP 'p cnf \K\d+' $*.cnf))
	$(eval UNICORNCLAUSES := $(shell grep -oP 'p cnf \d+ \K\d+' $*.cnf))
	$(eval CBMCVARS := $(shell grep -oP 'p cnf \K\d+' $*.cnf2))
	$(eval CBMCCLAUSES := $(shell grep -oP 'p cnf \d+ \K\d+' $*.cnf2))
	@echo name : $* > $@
	@echo unroll : $(UNROLL) >> $@
	@echo solutions : $(SOLUTIONS) >> $@
	@echo -n "btormc-time : " >> $@
	timeout 5m bash $(MYTIME) $(BTORMC) -kmax $(UNROLL) $*.btor2 >> $@ || echo timeout >> $@
	@echo -n "unicorn-boolector-time : " >> $@
	timeout 5m bash $(MYTIME) $(UNICORN) beator $*.m -u $(UNROLL) -p -s boolector --fast-minimize >> $@ || echo timeout >> $@
	@echo -n "unicorn-z3-time : " >> $@ 
	timeout 5m bash $(MYTIME) $(UNICORN) beator $*.m -u $(UNROLL) -p -s z3 --fast-minimize >> $@ || echo timeout >> $@
	@echo -n "unicorn-kissat-time : " >> $@
	timeout 5m bash $(MYTIME) $(UNICORN) beator $*.m -u $(UNROLL) -p --sat-solver kissat --discretize-memory >> $@ || echo timeout >> $@
	@echo -n "unicorn-cadical-time : " >> $@
	timeout 5m bash $(MYTIME) $(UNICORN) beator $*.m -u $(UNROLL) -p --sat-solver cadical --discretize-memory >> $@ || echo timeout >> $@
	@echo -n "klee-time : " >> $@
	timeout 5m bash $(MYTIME) $(KLEE) $*.bc >> $@ || echo timeout >> $@
	@echo -n "minisat-unicorn : " >> $@
	timeout 5m bash $(MYTIME) $(MINISAT) $*.cnf >> $@ || echo timeout >> $@
	@echo -n "minisat-cbmc : " >> $@
	timeout 5m bash $(MYTIME) $(MINISAT) $*.cnf2 >> $@ || echo timeout >> $@
	@echo -n "unicorn-vars : $(UNICORNVARS)\n" >> $@
	@echo -n "unicorn-clauses : $(UNICORNCLAUSES)\n" >> $@
	@echo -n "cbmc-vars : $(CBMCVARS)\n" >> $@
	@echo -n "cbmc-clauses : $(CBMCCLAUSES)\n" >> $@

