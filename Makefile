# broken !
program:
	mkdir -p bin
	cd src && ghc --make -fglasgow-exts -package wx -XNPlusKPatterns -XOverlappingInstances -XUndecidableInstances UTP2.lhs -o ../bin/UTP2run

all: program doc

doc:
	pdflatex -output-directory doc/styles doc/UTP2-MAIN.tex
	pdflatex -output-directory doc/styles doc/UTP2-MAIN.tex
	mkdir -p bin
	mv doc/styles/UTP2-MAIN.pdf bin/

clean:
	rm src/*.hi src/*.o doc/styles/*.aux doc/styles/*.toc doc/styles/*.log > /dev/null 2>&1

profile:
	cd src && ghc  --make -fglasgow-exts -package wx -prof -auto-all SAOITHIN.lhs -o ../bin/Saoithin.exe

uninstall:
	echo "Not supported yet"

install:
	echo "Not supported yet"
