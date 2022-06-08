SELFIE = selfie
UNICORN = ../target/debug/unicorn
MINISAT = minisat
BTORMC = btormc

# (1) Input is C source:
SRCS := $(wildcard *.c)
OBJS := $(patsubst %.c,%.m,$(SRCS))
BTORS := $(patsubst %.c,%.btor2,$(SRCS))
CNFS := $(patsubst %.c,%.cnf,$(SRCS))
QUBOS := $(patsubst %.c,%.qubo,$(SRCS))
DATAS_FROM_C := $(patsubst %.c,%.data1,$(SRCS))

# (2) Input is DIMACS CNF file:
DIMACS := $(foreach x,$(wildcard *.cnf),$(if $(filter $x,$(CNFS)),,$x))
DATAS_FROM_CNF := $(patsubst %.cnf,%.data2,$(DIMACS))

.PHONY: all clean obj btor2 cnf qubo

all: data.csv
	@column -s, -t $<

clean:
	rm -f data.csv
	rm -f $(OBJS)
	rm -f $(BTORS)
	rm -f $(CNFS)
	rm -f $(QUBOS)
	rm -f $(DATAS_FROM_C)
	rm -f $(DATAS_FROM_CNF)

obj: $(OBJS)
btor2: $(BTORS)
cnf: $(CNFS)
qubo: $(QUBOS)

data.csv: $(DATAS_FROM_C) $(DATAS_FROM_CNF)
	@echo "name,#sat,smt-time,cnf-vars,cnf-clauses,cnf-clause-var-ratio,sat-conflicts,sat-time,qubo-qbits,qubo-conn" > $@
	@for f in $^; do \
	  num_vars=$$(grep -oP 'Number of variables: \s+\K\d+' $$f);               \
	  num_clauses=$$(grep -oP 'Number of clauses: \s+\K\d+' $$f);              \
	  ratio_clause_var=$$(echo "scale=6; $$num_clauses / $$num_vars" | bc);    \
	  echo -n $$(grep -oP 'name : \K\S+' $$f),                          >> $@; \
	  echo -n $$(grep -oP 'solutions : \K\S+' $$f),                     >> $@; \
	  echo -n $$(grep -oP 'btormc-time : \K\S+' $$f),                   >> $@; \
	  echo -n $$num_vars,                                               >> $@; \
	  echo -n $$num_clauses,                                            >> $@; \
	  echo -n $$ratio_clause_var,                                       >> $@; \
	  echo -n $$(grep -oP 'conflicts\s+: \K\d+' $$f),                   >> $@; \
	  echo -n $$(grep -oP 'CPU time\s+: \K\S+' $$f),                    >> $@; \
	  echo -n $$(grep -oP 'number of qubits\s+: \K\d+' $$f),            >> $@; \
	  echo -n $$(grep -oP 'qubit connectivity\s+: avg=\K[\d.]+' $$f),   >> $@; \
	  echo >> $@; \
	done

%.m: %.c
	$(SELFIE) -c $< -o $@ > /dev/null

%.btor2: %.m
	$(eval UNROLL := $(shell grep -oP '// @UNROLL = \K\d+' $*.c))
	$(UNICORN) beator $< -o $@ -u $(UNROLL) -p -s boolector

%.cnf: %.m
	$(eval UNROLL := $(shell grep -oP '// @UNROLL = \K\d+' $*.c))
	$(UNICORN) beator $< -o $@ -u $(UNROLL) -p -s boolector -b -d

%.qubo: %.m
	$(eval UNROLL := $(shell grep -oP '// @UNROLL = \K\d+' $*.c))
	$(UNICORN) qubot $< -o $@ -u $(UNROLL) -s boolector

# (1) Pipeline starts from RISC-U binary:
%.data1: %.btor2 %.cnf %.m
	@echo name : $* > $@
	@echo solutions : $(shell grep -oP '// @SOLUTIONS = \K\d+' $*.c) >> $@
	@echo -n "btormc-time : " >> $@
	./mytime.sh $(BTORMC) -kmax 100 $*.btor2 >> $@
	$(MINISAT) $*.cnf | tee -a $@
	$(eval UNROLL := $(shell grep -oP '// @UNROLL = \K\d+' $*.c))
	$(UNICORN) qubot $*.m -u $(UNROLL) -s boolector >/dev/null 2>>$@

# (2) Pipeline starts from CNF file:
%.data2: %.cnf
	@echo name : $* > $@
	$(MINISAT) $*.cnf | tee -a $@
	$(UNICORN) qubot $*.cnf --from-dimacs >/dev/null 2>>$@
