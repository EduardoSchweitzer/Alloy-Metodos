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

fun pai [p: Pessoa, t: Tempo]: Pessoa {
	p.(pais[t]) & Homem
}

fun mae [p: Pessoa, t: Tempo]: Pessoa {
	p.(pais[t]) & Mulher
}

fun descendentes [ p : Pessoa,  t : Tempo] : set Pessoa {
	p.^(filhos.t)
}

fun relativosSangue[p: Pessoa, t: Tempo]: set Pessoa {
	 p.^(filhos.t) + p.^(pais[t]) + p.irmaos.Tempo
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
	// Nenhuma pessoa pode ser conjuge de um relativo de sangue
	no p : Casado | p.conjuge.Tempo in relativosSangue[p, Tempo]
	
	// Toda pessoa só pode ter, no máximo, um pai e uma mãe
	all p : Pessoa | lone pai[p ,Tempo] and lone mae[p, Tempo]
	
	// Nenhuma pessoa pode ser descendente de si mesma
	no p : Pessoa | p in p.^(pais[Tempo]) or p->Tempo in p.filhos
	
	// Nenhuma pessoa pode ser conjuge de si mema
	no p : Pessoa | p.conjuge.Tempo = p
	
	// Todos casados devem ser conjuge de uma pessoa do sexo oposto
	all p: Casado | (p in Homem => p.conjuge in Mulher -> Tempo) and (p in Mulher => p.conjuge in Homem -> Tempo)
	
	// Os filhos de uma pessoa são aqueles que a tem como pai/mãe
	all p: Pessoa | p.filhos.Tempo = {q: Pessoa | p in q.(pais[Tempo])}

	// Os irmãos de uma pessoa são aqueles que tem ou o mesmo pai, ou a mesma mãe.
	all p: Pessoa | p.irmaos.Tempo = ({q: Pessoa | pai[p, Tempo] = pai[q, Tempo] or mae[p, Tempo] = mae[q, Tempo]}) - (p)

	// Todo casado p é conjuge de q e q é conjuge de p
	all p: Casado | one q: Casado | (p.conjuge.Tempo = q) and (q.conjuge.Tempo = p)
}

run {
some Homem & Casado 
some Mulher
} for 5
