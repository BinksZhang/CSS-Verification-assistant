make:
	coqc util.v
	coqc Aux.v
	coqc state.v
	coqc language.v
	coqc semantic.v
	coqc CSSsVerification.v
