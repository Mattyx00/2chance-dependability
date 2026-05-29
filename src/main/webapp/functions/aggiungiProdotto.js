let nSpecifiche = 0;

function nuovaRiga(){
    let placeholder1 = "nome specifica " + (nSpecifiche+1);
    let placeholder2 = "valore specifica " + (nSpecifiche+1);
    
    const table = document.getElementById("aggiuntaProdotto");
    const container = table.querySelector("tbody") || table;
    const rows = container.getElementsByTagName("tr");
    
    // Insert before the "Aggiungi Specifica" button row (second to last row)
    const targetRow = rows[rows.length - 2];
    
    const newRow = document.createElement("tr");
    newRow.className = "specifica";
    newRow.innerHTML = `<td><input class="nome-specifica" type="text" placeholder="${placeholder1}" required></td> <td><input class="valore-specifica" type="text" placeholder="${placeholder2}" required></td>`;
    
    container.insertBefore(newRow, targetRow);
    nSpecifiche++;
}

function loadDropDown(categorie){
    const select = document.getElementById('categorie');
    for(let i=0; i<categorie.length; i++){
        var opt = document.createElement('option');
        opt.value = categorie[i];
        opt.innerHTML = categorie[i];
        select.appendChild(opt);
    }
}

document.addEventListener("DOMContentLoaded", function() {
    let xhttp = new XMLHttpRequest();
    xhttp.onreadystatechange = function() {
        if (this.readyState == 4 && this.status == 200) {
            loadDropDown((JSON.parse(this.response)).categorie);
        }
    };
    let url = "AdminServlet/mostraCategorie";
    xhttp.open("GET", url, true);
    xhttp.send();
});

function salvaProdotto(){
    let marca = document.getElementById("marca").value;
    let modello = document.getElementById("modello").value;
    let categoria = document.getElementById("categorie").value;
    let prezzo = document.getElementById("prezzo").value;
    let peso = document.getElementById("peso").value;
    let dimensioni = document.getElementById("dimensioni").value;
    let descrizione = document.getElementById("descrizione").value;
    let file = document.getElementById("immagine").files[0];

    let json_def = { specifiche: [] };
    
    document.querySelectorAll(".specifica").forEach(function (obj) {
       let nome = obj.querySelector(".nome-specifica").value;
       let valore = obj.querySelector(".valore-specifica").value;
       json_def.specifiche.push({ nome: nome, valore: valore });
    });

    let json_str = JSON.stringify(json_def);

    var formData = new FormData();
    formData.append('immagine', file);
    formData.append('specifiche', json_str);
    
    let url = `AdminServlet/aggiungiProdotto?marca=${encodeURIComponent(marca)}&modello=${encodeURIComponent(modello)}&prezzo=${encodeURIComponent(prezzo)}&descrizione=${encodeURIComponent(descrizione)}&dimensioni=${encodeURIComponent(dimensioni)}&peso=${encodeURIComponent(peso)}&categoria=${encodeURIComponent(categoria)}`;

    let xhttp = new XMLHttpRequest();
    xhttp.open("POST", url, true);
    xhttp.onreadystatechange = function() {
        if (this.readyState == 4) {
            if (this.status == 200) {
                alert("Prodotto aggiunto con successo!");
                window.location.replace("dashboard.jsp");
            } else {
                alert("Errore durante il salvataggio del prodotto.");
            }
        }
    };
    xhttp.send(formData);
}