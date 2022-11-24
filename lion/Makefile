SELFIE = selfie
UNICORN = ../target/release/unicorn
MINISAT = minisat
BTORMC = btormc
MYTIME = ../tools/mytime.sh

SRCS := $(wildcard *.c)
OBJS := $(patsubst %.c,%.m,$(SRCS))
BTORS := $(patsubst %.c,%.btor2,$(SRCS))
CNFS := $(patsubst %.c,%.cnf,$(SRCS))
DATAS := $(patsubst %.c,%.data,$(SRCS))

.PHONY: all clean obj btor2 cnf

all: data.csv
	@column -s, -t $<

clean:
	rm -f data.csv
	rm -f $(OBJS)
	rm -f $(BTORS)
	rm -f $(CNFS)
	rm -f $(DATAS)

obj: $(OBJS)
btor2: $(BTORS)
cnf: $(CNFS)

data.csv: $(DATAS)
	@echo "name,#unroll,#sat,btormc,unicorn+boolector" > $@
	@for f in $^; do \
	  echo -n $$(grep -oP 'name : \K\S+' $$f),                          >> $@; \
	  echo -n $$(grep -oP 'unroll : \K\S+' $$f),                        >> $@; \
	  echo -n $$(grep -oP 'solutions : \K\S+' $$f),                     >> $@; \
	  echo -n $$(grep -oP 'btormc-time : \K\S+' $$f),                   >> $@; \
	  echo -n $$(grep -oP 'unicorn-boolector-time : \K\S+' $$f),        >> $@; \
	  echo >> $@; \
	done

%.m: %.c
	$(SELFIE) -c $< -o $@ > /dev/null

# Generates a non-unrolled non-optimized BTOR2 file.
%.btor2: %.m
	$(UNICORN) beator $< -o $@

# Generates an unrolled constant-folded bit-blasted CNF file.
%.cnf: %.m
	$(eval UNROLL := $(shell grep -oP '// @UNROLL = \K\d+' $*.c))
	$(UNICORN) beator $< -o $@ -u $(UNROLL) -p -b -d

%.data: %.btor2 %.m
	$(eval UNROLL := $(shell grep -oP '// @UNROLL = \K\d+' $*.c))
	$(eval SOLUTIONS := $(shell grep -oP '// @SOLUTIONS = \K\d+' $*.c))
	@echo name : $* > $@
	@echo unroll : $(UNROLL) >> $@
	@echo solutions : $(SOLUTIONS) >> $@
	@echo -n "btormc-time : " >> $@
	$(MYTIME) $(BTORMC) -kmax $(UNROLL) $*.btor2 >> $@
	@echo -n "unicorn-boolector-time : " >> $@
	$(MYTIME) $(UNICORN) beator $*.m -u $(UNROLL) -p -s boolector --fast-minimize >> $@
	#$(MINISAT) $*.cnf | tee -a $@
