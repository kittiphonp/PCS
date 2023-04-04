####  Makefile for compilation on Linux  ####

OPT=-Ofast     # Optimization option by default

PRIME=P751_3_1

CDIR=${PRIME}
CURVE=$(word 1, $(subst _, " ", ${CDIR}))

CC=clang

ARCHITECTURE=_AMD64_
USE_OPT_LEVEL=_FAST_


MULX=-D _MULX_
ADX=-D _ADX_

ADDITIONAL_SETTINGS=-fwrapv -fomit-frame-pointer -march=native -madx -mbmi2 -fopenmp -pthread -DPARALLEL -DNEWSTRAT 

AR=ar rcs
RANLIB=ranlib

INC_DIR+= -I./src -I./src/$(CDIR) 
CFLAGS=$(OPT) $(ADDITIONAL_SETTINGS) -D $(ARCHITECTURE) -D __LINUX__ -D $(USE_OPT_LEVEL) $(MULX) $(ADX) $(INC_DIR) -D$(CURVE) -D$(CDIR)
LDFLAGS=-lm
ifeq "$(USE_OPT_LEVEL)" "_GENERIC_"
    EXTRA_OBJECTS_503=objs503/fp_generic.o
    EXTRA_OBJECTS_751=objs751/fp_generic.o
else ifeq "$(USE_OPT_LEVEL)" "_FAST_"
ifeq "$(ARCHITECTURE)" "_AMD64_"
    EXTRA_OBJECTS_${CURVE}=objs${CURVE}/fp_x64.o objs${CURVE}/fp_x64_asm.o
else ifeq "$(ARCHITECTURE)" "_ARM64_"
    EXTRA_OBJECTS_503=objs503/fp_arm64.o
    EXTRA_OBJECTS_751=objs751/fp_arm64.o objs751/fp_arm64_asm.o
endif
endif
OBJECTS_${CURVE}=objs${CURVE}/${CURVE}.o $(EXTRA_OBJECTS_${CURVE}) objs/random.o objs/fips202.o

all: lib${CURVE} tests KATS

objs${CURVE}/%.o: src/${CDIR}/%.c
	@mkdir -p $(@D)
	$(CC) -c $(CFLAGS) $< -o $@

ifeq "$(USE_OPT_LEVEL)" "_GENERIC_"
    objs503/fp_generic.o: src/P503/generic/fp_generic.c
	    $(CC) -c $(CFLAGS) src/P503/generic/fp_generic.c -o objs503/fp_generic.o

    objs751/fp_generic.o: src/P751/generic/fp_generic.c
	    $(CC) -c $(CFLAGS) src/P751/generic/fp_generic.c -o objs751/fp_generic.o
else ifeq "$(USE_OPT_LEVEL)" "_FAST_"
ifeq "$(ARCHITECTURE)" "_AMD64_"
    objs${CURVE}/fp_x64.o: src/${CDIR}/AMD64/fp_x64.c
		$(CC) -c $(CFLAGS) src/${CDIR}/AMD64/fp_x64.c -o objs${CURVE}/fp_x64.o

    objs${CURVE}/fp_x64_asm.o: src/${CDIR}/AMD64/fp_x64_asm.S
		$(CC) -c $(CFLAGS) src/${CDIR}/AMD64/fp_x64_asm.S -o objs${CURVE}/fp_x64_asm.o
else ifeq "$(ARCHITECTURE)" "_ARM64_"
    objs503/fp_arm64.o: src/P503/ARM64/fp_arm64.c
	    $(CC) -c $(CFLAGS) src/P503/ARM64/fp_arm64.c -o objs503/fp_arm64.o

    objs751/fp_arm64.o: src/P751/ARM64/fp_arm64.c
	    $(CC) -c $(CFLAGS) src/P751/ARM64/fp_arm64.c -o objs751/fp_arm64.o

    objs751/fp_arm64_asm.o: src/P751/ARM64/fp_arm64_asm.S
	    $(CC) -c $(CFLAGS) src/P751/ARM64/fp_arm64_asm.S -o objs751/fp_arm64_asm.o
endif
endif

objs/random.o: src/random/random.c
	@mkdir -p $(@D)
	$(CC) -c $(CFLAGS) src/random/random.c -o objs/random.o

objs/fips202.o: src/sha3/fips202.c
	$(CC) -c $(CFLAGS) src/sha3/fips202.c -o objs/fips202.o

lib${CURVE}: $(OBJECTS_${CURVE})
	rm -rf lib${CURVE} sike${CURVE} sidh${CURVE}
	mkdir lib${CURVE} sike${CURVE} sidh${CURVE}
	$(AR) lib${CURVE}/libsidh.a $^
	$(RANLIB) lib${CURVE}/libsidh.a


tests: lib${CURVE}
	$(CC) $(CFLAGS) -L./lib${CURVE} tests/arith_tests-${CURVE}.c tests/test_extras.c -lsidh $(LDFLAGS) -o arith_tests-${CURVE} $(ARM_SETTING)
	$(CC) $(CFLAGS) -L./lib${CURVE} tests/test_SIDH${CURVE}.c tests/test_extras.c -lsidh $(LDFLAGS) -o sidh${CURVE}/test_SIDH $(ARM_SETTING)
	$(CC) $(CFLAGS) -L./lib${CURVE} tests/test_SIKE${CURVE}.c tests/test_extras.c -lsidh $(LDFLAGS) -o sike${CURVE}/test_SIKE $(ARM_SETTING)
	$(CC) $(CFLAGS) -L./lib${CURVE} tests/arith_tests-${CURVE}.c tests/test_extras.c -lsidh $(LDFLAGS) -o sike${CURVE}/arith_test $(ARM_SETTING)

# AES
AES_OBJS=objs/aes.o objs/aes_c.o

objs/%.o: tests/aes/%.c
	@mkdir -p $(@D)
	$(CC) -c $(CFLAGS) $< -o $@

lib${CURVE}_for_KATs: $(OBJECTS_${CURVE}) $(AES_OBJS)
	$(AR) lib${CURVE}/libsidh_for_testing.a $^
	$(RANLIB) lib${CURVE}/libsidh_for_testing.a

KATS: lib${CURVE}_for_KATs
	$(CC) $(CFLAGS) -L./lib${CURVE} tests/PQCtestKAT_kem${CURVE}.c tests/rng/rng.c -lsidh_for_testing $(LDFLAGS) -o sike${CURVE}/PQCtestKAT_kem $(ARM_SETTING)

check: tests

.PHONY: clean

clean:
	rm -rf *.req objs* objs lib* sidh* sike* arith_tests-*

