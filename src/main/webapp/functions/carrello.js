function eliminaProdotto(idprodotto){
    let xhttp = new XMLHttpRequest();
    xhttp.onreadystatechange = function() {
        if (this.readyState == 4 && this.status == 200) {
            location.reload();
        }
    };
    let url = "EditCarrello?tipo=elimina&prodotto="+idprodotto;
    xhttp.open("GET", url, true);
    xhttp.send();
}

$(".quantitaProdottoCarrello").bind('keyup mouseup', function () {
    $(this).prop("disabled", true);
    let mioelemento = this;
    let xhttp = new XMLHttpRequest();
    xhttp.onreadystatechange = function() {
        if (this.readyState == 4 && this.status == 200) {
            $(mioelemento).prop("disabled", false);
        }
    };
    let url = "EditCarrello?tipo=cambiaquantita&prodotto="+$(this).attr("prodotto")+"&quantita="+$(this).val();
    url = url.replace(/\s+/g, '');

    xhttp.open("GET", url, true);
    xhttp.send();
});

function acquista(){
    if($(".prodottoCarrello").length<1){
        alert("Impossibile acquistare un carrello vuoto!");
        event.preventDefault(); //ferma l'action del form
        return;
    }
    let indirizzo = prompt("Inserisci l'indirizzo: ", "Via roma 129");
    if(indirizzo == ""){
        alert("Inserire un indirizzo valido!");
        event.preventDefault();
        return;
    }
    $("#indirizzo").val(indirizzo);
}
