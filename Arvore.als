open util/ordering [Tempo] as T

sig Tempo{}

abstract sig Pessoa {
filhos: set Pessoa -> Tempo,
irmaos: set Pessoa -> Tempo,
conjuge : Pessoa lone -> Tempo,
vivo : set Tempo

}

sig Homem, Mulher extends Pessoa {}

fun pais [ t : Tempo] : Pessoa -> Pessoa  {
	~(filhos.t)
}

fun tios [ t : Tempo] :  Pessoa -> Pessoa{
	(pais.t).irmaos
}

fun netos [ p: Pessoa, t : Tempo] : set Pessoa {
	p.filhos.filhos
}

fun avos [ p : Pessoa] : set Pessoa {
	p.pais.pais
}

fun descendentes [ p : Pessoa] : set Pessoa {
	p.^filhos
}

fun primos [p : Pessoa ] : set Pessoa  {
	p.tios.filhos
}

pred AddFilho [ p : Pessoa, h: Homem, m: Mulher, t,t1 : Tempo] {
	-- Pre-condição
	h+m in vivo.t
	p !in vivo.t
	--pos-condição
	vivo.t1 = vivo.t + p
	h.filhos.t1 = h.filhos.t + p
	m.filhos.t1 = m.filhos.t + p
	--não muda
	
}

pred Casamento[ p1, p2 : Pessoa, t,t1 : Tempo] {
	-- Pre-condição
	p1+p2 in vivo.t
	p1.conjuge.t != p2
	p2.conjuge.t != p1
	--pos-condição
	p1.conjuge.t1 = p2
	p2.conjuge.t1 = p1
	--não muda
	p1+p2 in vivo.t 
	p1+p2 in vivo.t1
}

pred Divorcio[ p1, p2 : Pessoa, t,t1 : Tempo] {
	-- Pre-condição
	p1+p2 in vivo.t
	p1.conjuge.t = p2
	p2.conjuge.t = p1
	--pos-condição
	p1.conjuge.t1 != p2
	p2.conjuge.t1 != p1
	--não muda
	p1+p2 in vivo.t 
	p1+p2 in vivo.t1

}
fact {
	no p : Pessoa | p.conjuge in p.irmaos
	all p : Pessoa | (lone (p.pais & Homem) and (lone p.pais & Mulher))
	no p : Pessoa | p in p.^pais
	all p : Pessoa |  p.primos = {q : Pessoa | p.tios = q.pais}
	no p : Pessoa | p.conjuge = p
	no p : Pessoa | p.conjuge in p.irmaos

}

