# broken !
all: program doc

doc:
	pdflatex -output-directory doc/styles doc/Saoithin-MAIN.tex
	pdflatex -output-directory doc/styles doc/Saoithin-MAIN.tex
	mkdir -p bin
	mv doc/styles/Saoithin-MAIN.pdf bin/

program:
	mkdir -p bin
	cd src && ghc  --make -fglasgow-exts -package wx -XNPlusKPatterns -XOverlappingInstances -XUndecidableInstances SAOITHIN.lhs -o ../bin/Saoithin.exe

clean:
	rm src/*.hi src/*.o doc/styles/*.aux doc/styles/*.toc doc/styles/*.log > /dev/null 2>&1

profile:
	cd src && ghc  --make -fglasgow-exts -package wx -prof -auto-all SAOITHIN.lhs -o ../bin/Saoithin.exe

uninstall:
	echo "Not supported yet"

install:
	echo "Not supported yet"
