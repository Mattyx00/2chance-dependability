let id_prodotto_global = 0;

function salvaModificaProdotto(){
    let marca = document.getElementById("marca").value;
    let modello = document.getElementById("modello").value;
    let categoria = document.getElementById("categorie").value;
    let prezzo = document.getElementById("prezzo").value;
    let peso = document.getElementById("peso").value;
    let dimensioni = document.getElementById("dimensioni").value;
    let descrizione = document.getElementById("descrizione").value;
    let file = document.getElementById("immagine");

    let json_def = { specifiche: [] };
    document.querySelectorAll(".specifica").forEach(function (obj) {
        let nome = obj.querySelector(".nome-specifica").value;
        let valore = obj.querySelector(".valore-specifica").value;
        json_def.specifiche.push({ nome: nome, valore: valore });
    });

    let json_str = JSON.stringify(json_def);

    var formData = new FormData();
    if(file.files.length > 0) {
        formData.append('immagine', file.files[0]);
    }
    formData.append('specifiche', json_str);

    let url = `AdminServlet/modificaProdotto?marca=${encodeURIComponent(marca)}&modello=${encodeURIComponent(modello)}&prezzo=${encodeURIComponent(prezzo)}&descrizione=${encodeURIComponent(descrizione)}&dimensioni=${encodeURIComponent(dimensioni)}&peso=${encodeURIComponent(peso)}&categoria=${encodeURIComponent(categoria)}&id=${id_prodotto_global}`;
    
    let xhttp = new XMLHttpRequest();
    xhttp.open("POST", url, true);
    xhttp.onreadystatechange = function() {
        if (this.readyState == 4) {
            if (this.status == 200) {
                alert("Prodotto modificato con successo!");
                window.location.replace("dashboard.jsp");
            } else {
                alert("Errore durante la modifica del prodotto.");
            }
        }
    };
    xhttp.send(formData);
}

function riempiForm(jsonProdotto){
    document.getElementById("marca").value = jsonProdotto.marca;
    document.getElementById("modello").value = jsonProdotto.modello;
    document.getElementById("categorie").value = jsonProdotto.categoria;
    document.getElementById("prezzo").value = jsonProdotto.prezzo;
    document.getElementById("peso").value = jsonProdotto.peso;
    document.getElementById("dimensioni").value = jsonProdotto.dimensioni;
    document.getElementById("descrizione").value = jsonProdotto.descrizione;

    let specifiche = jsonProdotto.specifiche;
    const table = document.getElementById("aggiuntaProdotto");
    const container = table.querySelector("tbody") || table;
    const rows = container.getElementsByTagName("tr");
    
    // Insert before the "Aggiungi Specifica" button row (second to last row)
    const targetRow = rows[rows.length - 2];

    for(let i=0; i<specifiche.length; i++){
        let placeholder1 = "nome specifica " + (i);
        let placeholder2 = "valore specifica " + (i);
        let nome = specifiche[i].nome;
        let valore = specifiche[i].valore;
        
        const newRow = document.createElement("tr");
        newRow.className = "specifica";
        newRow.innerHTML = `<td><input class="nome-specifica" type="text" value="${nome}" placeholder="${placeholder1}" required></td> <td><input class="valore-specifica" type="text" value="${valore}" placeholder="${placeholder2}" required></td>`;
        
        container.insertBefore(newRow, targetRow);
    }
    
    // Update counter in the global namespace (from aggiungiProdotto.js)
    if (typeof nSpecifiche !== 'undefined') {
        nSpecifiche = specifiche.length;
    }
}

document.addEventListener("DOMContentLoaded", function (){
    document.documentElement.style.cursor = 'wait';

    const queryString = window.location.search;
    const urlParams = new URLSearchParams(queryString);
    const id_prodotto = urlParams.get('idProdotto');
    if(id_prodotto==null||id_prodotto==""){
        window.location.replace("WEB-INF/error-pages/notfound.jsp");
        return;
    }

    let xhttp = new XMLHttpRequest();
    xhttp.onreadystatechange = function() {
        if (this.readyState == 4 && this.status == 200) {
            document.documentElement.style.cursor = 'default';
            riempiForm(JSON.parse(this.response));
        }
    };
    id_prodotto_global = id_prodotto;
    let url = "AdminServlet/getProdotto?idProdotto="+id_prodotto;
    xhttp.open("GET", url, true);
    xhttp.send();
});