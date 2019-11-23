COQC =/mnt/c/Coq/bin/coqc.exe



%.vo: %.v
	$(COQC) $<

tidy :
	find \( -iname '.*.aux' -or -iname '*.glob' \) -exec rm -f '{}' \;

clean:
	find \( -iname '.*.aux' -or -iname '*.glob' -or -iname '*.vo' \) -exec rm -f '{}' \;
