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

// Os avós de uma pessoa P são aqueles que tem como filho um dos pais de P
fun avos [p: Pessoa, t: Tempo] : set Pessoa {
	{q: Pessoa | pai[p, t] in q.(filhos.t) or mae[p, t] in q.(filhos.t)}
}

// Os netos de uma pessoa P são aqueles que tem como pai um dos filhos de P
fun netos [p: Pessoa, t: Tempo] : set Pessoa {
	{q: Pessoa | pai[q, t] in p.(filhos.t) or mae[q, t] in p.(filhos.t)}
}

fun relativosSangue[p: Pessoa, t: Tempo]: set Pessoa {
	 p.^(filhos.t) + p.^(pais[t]) + p.irmaos.Tempo
}

pred EstaVivo [p: Pessoa, t: Tempo] {
	t in p.vivo
}

pred AddFilho [ p : Pessoa, h: Homem, m: Mulher, t,t1 : Tempo] {
	-- Pre-condição
	EstaVivo[h, t]
	EstaVivo[m, t]
	!EstaVivo[p, t]
	
	h.conjuge.t = m
	m.conjuge.t = h
	--pos-condição
	EstaVivo[p, t1]
	h.filhos.t1 = h.filhos.t + p
	m.filhos.t1 = m.filhos.t + p
	--não muda
	EstaVivo[h, t1]
	EstaVivo[m, t1]
	h.conjuge.t1 = m
	m.conjuge.t1 = h	
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

	// Nenhuma pessoa pode estar morta e depois estar viva novamente
	no p: Pessoa | all t: Tempo | !EstaVivo[p, t] and EstaVivo[p, T/next[t]]

	// Nnehuma pessoa pode deixar de ser filho de alguem
	no p: Pessoa | some q: Pessoa | q in p.(pais[Tempo]) and !(q in p.(pais[T/next[Tempo]]))
}

run {
some pais[Tempo]
some netos[Pessoa, Tempo]
some Pessoa.filhos
} for 5
