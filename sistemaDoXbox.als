/*
			Tema 2: Sistema do videogame Xbox
	
	(✓)	Seu sistema operacional é dividido em três páginas: Meus jogos e apps, Social e Loja. 
	(✓)	Em “Meus jogos e apps”, cada Xbox pode possuir jogos e aplicativos diversos. 
	(✓)	Por conta de restrições memoria interna, considere que o Xbox pode armazenar até 5 jogos e 8 aplicativos.
 	(✓)	Em “Social”, são exibidas publicações de outros usuários. 
	(✓)	Estas publicações podem ser screenshots, vídeos ou transmissões ao vivo (streaming).
 	(✓)	Em cada publicação, o usuário tem a opção de curtir ou compartilhar.
	(✓)	No caso da transmissão ao vivo, o usuário ainda tem a opção de comentar a transmissão. 
	(✓)	Na página “Loja”, são exibidos os jogos que estão em promoção na Xbox Live, rede online do console. 
	(✓)	A cada semana, de 10 até 20 jogos entram em promoção. 
	(✓)	Cada jogo deve ter a opção de comprar. 
	(✓)	Entretanto, caso o Xbox já possua aquele jogo instalado, esta opção deve estar desabilitada.
*/

module sistemaDoXbox

--------------------------
----ASSINATURAS ----
--------------------------

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

----------------
----FATOS---- 
----------------

fact mult{

	all m : MeusJogosApps | one m.~jogosEApps
	all s : Social | one s.~social
	all l : Loja |  one l.~loja
	all jogo : JogoPromocao | one jogo.~jogos
	all jogo : JogoComprado |one jogo.~jogos
	all compra : Comprar | one compra.~comprado
	all publicacao : Publicacao | one publicacao.~publicacoes
	all comentario : Comentario | one comentario.~comentarios
	all curtida : Curtida | one curtida.~curtidas
	all compartilhamento : Compartilhamento | one compartilhamento.~compartilhamentos
	
}

fact jogosEAppsMaximosNoXbox{

	all pagina : MeusJogosApps | jogosMaximo[pagina] and appsMaximo[pagina]

}

fact usuarioNaoPodeComprarUmJogoQueJaTenha{

	all usuario : Usuario, loja : Loja | not jogosDoUsuario[usuario] in jogosDaLoja[loja]

}

fact sobreLoja{

	all loja : Loja | jogosPossiveisNaLoja[loja]

}

------------------------
----PREDICADOS---- 
------------------------

pred jogosMaximo[pagina : MeusJogosApps]{

	#jogosDaPagina[pagina] <= 5

}

pred appsMaximo[pagina : MeusJogosApps]{

	#appsDaPagina[pagina] <= 8

}

pred jogosPossiveisNaLoja[loja : Loja]{

	#jogosDaLoja[loja] >= 10 and #jogosDaLoja[loja] <= 20

}

--------------------
----FUNÇÕES---- 
--------------------


fun jogosDoUsuario[usuario : Usuario] : set Jogo{
	usuario.videoGame.jogosEApps.jogos
}

fun jogosDaLoja[loja : Loja]  : set Jogo{

	loja.jogos

}

fun jogosDaPagina[pagina : MeusJogosApps] : set Jogo{

	pagina.jogos

}

fun appsDaPagina[pagina : MeusJogosApps] : set Aplicativo{

	pagina.apps

}

--------------------------------
----ASSERTS / CHECKS----
--------------------------------


assert  testJogosMaximo{

	all pagina : MeusJogosApps |#jogosDaPagina[pagina] <= 5

}

check  testJogosMaximo for 15

assert testAppsMaximo{

	all pagina : MeusJogosApps |#appsDaPagina[pagina] <= 8

}

check testAppsMaximo for 15

assert testJogosPossiveisNaLoja{

	all loja : Loja | #jogosDaLoja[loja]>= 10 and #jogosDaLoja[loja] <= 20

}

check  testJogosPossiveisNaLoja for 15

----------------
----SHOW----
----------------

pred show[]{}
run show for 15



