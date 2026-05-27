foto_attuale = 0;
foto_totali = 0;


function contaFoto(){
	foto_totali = $("#carosello img").length - 1;
}

function abbreviaDesc(){
	let descrizioni = document.getElementsByClassName("descrizione-prodotto")
	for(i=0; i<descrizioni.length; i++){
		let testo = descrizioni[i].innerHTML;
		if(testo.length>20) descrizioni[i].innerHTML = testo.substring(0, 20) + "...";

	}

	let titolo = document.getElementsByClassName("titolo-prodotto")
	for(i=0; i<titolo.length; i++){
		let testo = titolo[i].innerHTML;
		if(testo.length>15) titolo[i].innerHTML = testo.substring(0, 15) + "...";
	}
}

function start(){
	contaFoto();
	abbreviaDesc();
}

function cambiaFoto(foto){
	$(`#carosello img`).eq(foto_attuale).removeClass("carosello-attiva");
	$(`#carosello img`).eq(foto_attuale).addClass("carosello-disattivata");
	if(foto=="precedente"){
		if(foto_attuale==0){
			foto_attuale = foto_totali;
		}else{
			foto_attuale--;
		}
	}else{
		if(foto_attuale==foto_totali){
			foto_attuale = 0;
		}else{
			foto_attuale++;
		}
	}

	let nextImg = $(`#carosello img`).eq(foto_attuale);
	let dataSrc = nextImg.attr("data-src");
	if (dataSrc && !nextImg.attr("src")) {
		nextImg.attr("src", dataSrc);
	}
	nextImg.removeClass("carosello-disattivata");
	nextImg.addClass("carosello-attiva");

}