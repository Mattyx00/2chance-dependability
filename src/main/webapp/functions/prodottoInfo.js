function show_box(info, element){
    $("#descrizione, #scheda-tecnica, #recensioni").removeClass("info-box-elemento-selezionato");
    $("#"+info).addClass("info-box-elemento-selezionato");
    $(".pulsante-controlli").removeClass("pulsante-controlli-selezionato");
    $(element).addClass("pulsante-controlli-selezionato");
}

function redirectConfronto(){
    let prodotto1 = localStorage.getItem("prodotto1");
    let prodotto2 = localStorage.getItem("prodotto2");

    window.location.href = 'ConfrontaServlet?prodotto1='+prodotto1+"&prodotto2="+prodotto2;
}

function confronta(idProdotto){
    //utilizzo il localStorage che permette di salvare valori nel browser
    if(localStorage.getItem("prodotto1") == null){
        alert("Primo prodotto aggiunto al confronto, scegline un altro!");
        localStorage.setItem("prodotto1", idProdotto);
    }else{
        if(localStorage.getItem("prodotto2") == null || localStorage.getItem("prodotto2") == "null"){
            alert("Secondo prodotto aggiunto al confronto");
            localStorage.setItem("prodotto2", idProdotto);
            redirectConfronto();
        }else{ //controllo aggiuntivo
            alert("Primo prodotto aggiunto al confronto, scegline un altro!");
            localStorage.setItem("prodotto1", idProdotto);
            localStorage.setItem("prodotto2", null);
        }
    }
}

let star = 1;

$("#stelle > i").click(function() {
    star = $(this).index() + 1;
    $(this).prevAll().addClass('yellow')
    $(this).addClass('yellow')
    $(this).nextAll().removeClass('yellow')
});


function aggiungiRecensione(idProdotto){
    let testo_recensione = $("#testo").val();
    let valutazione = star;

    let xhttp = new XMLHttpRequest();
    xhttp.onreadystatechange = function() {
        if (this.readyState == 4 && this.status == 200) {
            alert("Recensione aggiunta con successo!");
            location.reload();
        }
    };
    let url = "RecensioniServlet/aggiungiRecensione?testo="+testo_recensione+"&valutazione="+valutazione+"&idProdotto="+idProdotto;
    xhttp.open("GET", url, true);
    xhttp.send();
}