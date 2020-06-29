open util/ordering [Tempo] as T

sig Tempo{}

abstract sig Pessoa {
filhos:  Pessoa set -> Tempo,
irmaos:  Pessoa set -> Tempo,
vivo : set Tempo

}

sig Homem, Mulher extends Pessoa {}

sig Casado in Pessoa {
	conjuge : Pessoa lone -> Tempo
}

fun pais [ t : Tempo] : Pessoa -> Pessoa  {
	~(filhos.t)
}

fun descendentes [ p : Pessoa,  t : Tempo] : set Pessoa {
	p.^(filhos.t)
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
	all p : Pessoa | all t: Tempo | (lone (p.(pais[t]) & Homem) and (lone(p.(pais[t])  & Mulher)))
	no p : Pessoa | all t: Tempo | p in p.^(pais[t])
	no p : Pessoa | all t: Tempo | p.conjuge.t = p
	no p : Pessoa | p.conjuge in p.irmaos
}

run {} for 3
