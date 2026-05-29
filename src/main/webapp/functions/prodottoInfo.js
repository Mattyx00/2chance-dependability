function show_box(info, element){
    document.querySelectorAll("#descrizione, #scheda-tecnica, #recensioni").forEach(function(el) {
        el.classList.remove("info-box-elemento-selezionato");
    });
    let target = document.getElementById(info);
    if (target) {
        target.classList.add("info-box-elemento-selezionato");
    }
    document.querySelectorAll(".pulsante-controlli").forEach(function(el) {
        el.classList.remove("pulsante-controlli-selezionato");
    });
    if (element) {
        element.classList.add("pulsante-controlli-selezionato");
    }
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

document.addEventListener("DOMContentLoaded", function() {
    let stars = document.querySelectorAll("#stelle > i");
    stars.forEach(function(s, index) {
        s.addEventListener("click", function() {
            star = index + 1;
            stars.forEach(function(item, idx) {
                if (idx <= index) {
                    item.classList.add("yellow");
                } else {
                    item.classList.remove("yellow");
                }
            });
        });
    });
});

function aggiungiRecensione(idProdotto){
    let testo_recensione = document.getElementById("testo").value;
    let valutazione = star;

    let xhttp = new XMLHttpRequest();
    xhttp.onreadystatechange = function() {
        if (this.readyState == 4 && this.status == 200) {
            alert("Recensione aggiunta con successo!");
            location.reload();
        }else if (this.readyState == 4 && this.status == 401) {
            alert("Devi essere loggato per aggiungere una recensione.");
            window.location.href = "login.jsp";
        }
    };
    let url = "RecensioniServlet/aggiungiRecensione?testo="+encodeURIComponent(testo_recensione)+"&valutazione="+valutazione+"&idProdotto="+idProdotto;
    xhttp.open("GET", url, true);
    xhttp.send();
}