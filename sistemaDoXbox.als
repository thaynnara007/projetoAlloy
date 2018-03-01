module sistemaDoXbox

sig Usuario{

	acoes : set Acao,
	videoGame : one Xbox

}
sig Xbox{
	
	jogosEApps: one MeusJogosApps,
	social : one Social,
	loja : one Loja
}

one sig MeusJogosApps{
	
	jogos : set Jogo,
	apps : set Aplicativo 
}
one sig Social{
		
	publicacoes : set Publicacao
}
one sig Loja{

	jogos : some JogoPromocao
}
sig Jogo{}
sig JogoComprado extends Jogo{}
sig JogoInstalado in JogoComprado{}
sig JogoPromocao extends Jogo{}
sig Aplicativo{}
abstract sig Publicacao{

	curtidas : set Curtida, 
	compartilhamentos : set Compartilhamento
}
sig Screenshot extends Publicacao{}
sig Video extends Publicacao{}
sig Streaming extends Publicacao{

	comentarios : set Comentario
}
abstract sig Acao{}
sig Curtida extends Acao{}
sig Comentario extends Acao{}
sig Compartilhamento extends Acao{}

fact mult{
	all m:MeusJogosApps | one m.~jogosEApps
	all s:Social | one s.~social
	all l:Loja |  one l.~loja
}
fact jogosEAppsMaximosNoXbox{
	all pagina:MeusJogosApps | jogosMaximo[pagina] and appsMaximo[pagina]
}
fact usuarioNaoPodeComprarUmJogoQueJaTenha{
	all usuario: Usuario, loja : Loja | not jogosDoUsuario[usuario] in jogosDaLoja[loja]
}

pred jogosMaximo[pagina : MeusJogosApps]{
	#(pagina.jogos) <= 5
}

pred appsMaximo[pagina : MeusJogosApps]{
	#(pagina.apps) <= 8
}

fun jogosDoUsuario[usuario : Usuario] : set Jogo{
	usuario.videoGame.jogosEApps.jogos
}

fun jogosDaLoja[loja : Loja] : set Jogo{
	loja.jogos
}

fun ehStreaming[social : Social] : set Publicacao{
	social.publicacoes & Streaming
}

fun ehVideo[social : Social] : set Publicacao{
	social.publicacoes & Video
}

fun ehSreenshot[social : Social] : set Publicacao{
	social.publicacoes & Screenshot
												
}


pred show[]{}
run show for 3



