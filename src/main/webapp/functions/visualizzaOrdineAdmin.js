function loadInfoOrdine(jsonOrdine){
    jsonOrdine = jsonOrdine.prodotti;
    console.log(jsonOrdine);
    let container = document.getElementById("corpo-carrello");
    if (!container) return;
    for(let i=0; i<jsonOrdine.length; i++){
        let id=jsonOrdine[i].id, marca=jsonOrdine[i].marca, modello=jsonOrdine[i].modello, prezzo=jsonOrdine[i].prezzo, quantita=jsonOrdine[i].quantita;
        let prodottoCarrello = `<div class="prodottoCarrello"> <a href="ProdottoServlet?prodotto=${id}" class="infoProdottoCarrello" style="text-decoration: none; color: inherit;"> <p class="nomeProdottoCarrello">${marca} ${modello}</p> </a> <p class="prezzoProdottoCarrello">${prezzo}€</p><p>Quantita: ${quantita}</p> </div>`;
        container.insertAdjacentHTML('beforeend', prodottoCarrello);
    }
}

document.addEventListener("DOMContentLoaded", function (){
    const queryString = window.location.search;
    const urlParams = new URLSearchParams(queryString);
    const id_ordine = urlParams.get('ordine');
    if(id_ordine=="null"||id_ordine==null){
        window.location.href = ("WEB-INF/error-pages/notfound.jsp");
        return;
    }

    let xhttp = new XMLHttpRequest();
    xhttp.onreadystatechange = function() {
        if (this.readyState == 4 && this.status == 200) {
            loadInfoOrdine(JSON.parse(this.response));
        }
    };
    let url = "AdminServlet/infoOrdine?idOrdine="+id_ordine;
    xhttp.open("GET", url, true);
    xhttp.send();
});