nSpecifiche = 0;

function nuovaRiga(){
    let placeholder1 = "nome specifica " + (nSpecifiche+1);
    let placeholder2 = "valore specifica " + (nSpecifiche+1);
    $("#aggiuntaProdotto").find('tr:last').prev().prev().after('<tr class="specifica"> <td><input id="nome-specifica" type="text" placeholder="'+placeholder1+'" required></td> <td><input id = "valore-specifica" type="text" placeholder="'+placeholder2+'" required></td></tr>');
    nSpecifiche++;
}

function loadDropDown(categorie){
    select = document.getElementById('categorie');


    for(i=0; i<categorie.length; i++){
        var opt = document.createElement('option');
        opt.value = categorie[i];
        opt.innerHTML = categorie[i];
        select.appendChild(opt);
    }
}

$( document ).ready(function() {
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
    let marca = $("#marca").val();
    let modello = $("#modello").val();
    let categoria = $("#categorie").val();
    let prezzo = $("#prezzo").val();
    let peso = $("#peso").val();
    let dimensioni = $("#dimensioni").val();
    let descrizione = $("#descrizione").val();
    let file = document.getElementById("immagine");
    file = file.files[0];

    //let array_provv = new Array();
    let json_def = `{"specifiche":[]}`;
    json_def = JSON.parse(json_def);
    $(".specifica").each(function (i, obj){
       let nome = $(obj).find("#nome-specifica").val();
       let valore = $(obj).find("#valore-specifica").val();
       let json_provv = {nome:nome, valore: valore};
       json_def.specifiche.push(json_provv);
       //array_provv.push(json_provv);
    });

    json_def = JSON.stringify(json_def);


    var formData = new FormData();
    formData.append('immagine', file);
    formData.append('specifiche', json_def);
    let url = `AdminServlet/aggiungiProdotto?marca=${marca}&modello=${modello}&prezzo=${prezzo}&descrizione=${descrizione}&dimensioni=${dimensioni}&peso=${peso}&categoria=${categoria}`;
    //faccio una richiesta di tipo POST all'url creato passandogli il formData
    $.ajax({
        url: url,
        type:"POST",
        processData:false,
        contentType: false,
        data: formData,
        complete: function(data){
            alert("Prodotto aggiunto con successo!");
            window.location.replace("dashboard.jsp");
        }
    });

}