make:
	coqc util.v
	coqc Aid.v
	coqc state.v
	coqc language.v
	coqc semantic.v
	coqc CSSsVerification.v