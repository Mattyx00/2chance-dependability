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

document.addEventListener("DOMContentLoaded", function() {
    document.querySelectorAll(".quantitaProdottoCarrello").forEach(function(input) {
        let lastValue = input.value;
        let triggerUpdate = function() {
            let mioelemento = this;
            if (mioelemento.value === lastValue) return;
            lastValue = mioelemento.value;
            mioelemento.disabled = true;
            let xhttp = new XMLHttpRequest();
            xhttp.onreadystatechange = function() {
                if (this.readyState == 4 && this.status == 200) {
                    mioelemento.disabled = false;
                }
            };
            let prodottoId = mioelemento.getAttribute("prodotto").trim();
            let url = "EditCarrello?tipo=cambiaquantita&prodotto=" + prodottoId + "&quantita=" + mioelemento.value;
            xhttp.open("GET", url, true);
            xhttp.send();
        };
        input.addEventListener("change", triggerUpdate);
        input.addEventListener("keyup", triggerUpdate);
    });
});

function acquista(event){
    if(document.querySelectorAll(".prodottoCarrello").length < 1){
        alert("Impossibile acquistare un carrello vuoto!");
        if (event) event.preventDefault(); //ferma l'action del form
        return;
    }
    let indirizzo = prompt("Inserisci l'indirizzo: ", "Via roma 129");
    if(indirizzo === null || indirizzo.trim() === ""){
        alert("Inserire un indirizzo valido!");
        if (event) event.preventDefault();
        return;
    }
    document.getElementById("indirizzo").value = indirizzo;
}

