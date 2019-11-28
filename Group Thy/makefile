COQC =/mnt/c/Coq/bin/coqc.exe

basics:  defns  
	$(COQC) Basics.v

defns:  notions
	$(COQC) Defns.v

notions:
	$(COQC) Notions.v



%.vo: %.v
	$(COQC) $<

tidy :
	find \( -iname '.*.aux' -or -iname '*.glob' \) -exec rm -f '{}' \;

clean:
	find \( -iname '.*.aux' -or -iname '*.glob' -or -iname '*.vo' \) -exec rm -f '{}' \;
