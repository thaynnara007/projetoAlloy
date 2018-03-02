module sistemaDoXbox

sig Usuario{

	videoGame : one Xbox
}
sig Xbox{
	
	jogosEApps: one MeusJogosApps,
	social : one Social,
	loja : one Loja
}

one sig MeusJogosApps{
	
	jogos : set JogoComprado,
	apps : set Aplicativo 
}
one sig Social{
		
	publicacoes : some Publicacao
}
one sig Loja{

	jogos : some JogoPromocao,
	apps : some Aplicativo
}
abstract sig Jogo{}
sig JogoComprado extends Jogo{}
sig JogoPromocao extends Jogo{
	
	comprado : one Comprar
}
sig Aplicativo{}
abstract sig Publicacao{

	curtidas : one Curtida, 
	compartilhamentos : one Compartilhamento
}
sig Screenshot extends Publicacao{}
sig Video extends Publicacao{}
sig Streaming extends Publicacao{

	comentarios : set Comentario
}
sig Curtida {}
sig Comentario {}
sig Compartilhamento {} 
sig Comprar{}

fact mult{
-- 
	all m:MeusJogosApps | one m.~jogosEApps
	all s:Social | one s.~social
	all l:Loja |  one l.~loja
	all jogo:JogoPromocao | one jogo.~jogos
	all jogo:JogoComprado |one jogo.~jogos
	all compra:Comprar | one compra.~comprado
	all publicacao:Publicacao | one publicacao.~publicacoes
	all comentario:Comentario | one comentario.~comentarios
	all curtida:Curtida | one curtida.~curtidas
	all compartilhamento : Compartilhamento | one compartilhamento.~compartilhamentos
	
}
fact jogosEAppsMaximosNoXbox{
	all pagina:MeusJogosApps | jogosMaximo[pagina] and appsMaximo[pagina]
}
fact usuarioNaoPodeComprarUmJogoQueJaTenha{
	all usuario: Usuario, loja : Loja | not jogosDoUsuario[usuario] in jogosDaLoja[loja]
}
fact sobreLoja{
	all loja: Loja | jogosPossiveisNaLoja[loja]
}
pred jogosMaximo[pagina : MeusJogosApps]{
	#jogosDaPagina[pagina] <= 5
}

pred appsMaximo[pagina : MeusJogosApps]{
	#appsDaPagina[pagina] <= 8
}
pred jogosPossiveisNaLoja[loja : Loja]{
	#jogosDaLoja[loja]>= 10 and #jogosDaLoja[loja] <= 20
}

fun jogosDoUsuario[usuario : Usuario] : set Jogo{
	usuario.videoGame.jogosEApps.jogos
}

fun jogosDaLoja[loja : Loja] : set Jogo{
	loja.jogos
}
fun jogosDaPagina[pagina:MeusJogosApps] : set Jogo{
	pagina.jogos
}
fun appsDaPagina[pagina:MeusJogosApps] : set Aplicativo{
	pagina.apps
}


pred show[]{}
run show for 13



