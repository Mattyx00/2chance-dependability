let id_prodotto_global = 0;

function salvaModificaProdotto(){
    let marca = $("#marca").val();
    let modello = $("#modello").val();
    let categoria = $("#categorie").val();
    let prezzo = $("#prezzo").val();
    let peso = $("#peso").val();
    let dimensioni = $("#dimensioni").val();
    let descrizione = $("#descrizione").val();
    let file = document.getElementById("immagine");


    let json_def = `{"specifiche":[]}`;
    json_def = JSON.parse(json_def);
    $(".specifica").each(function (i, obj){
        let nome = $(obj).find("#nome-specifica").val();
        let valore = $(obj).find("#valore-specifica").val();
        let json_provv = {nome:nome, valore: valore};
        json_def.specifiche.push(json_provv);
    });

    json_def = JSON.stringify(json_def);


    var formData = new FormData();
    if(file.files.length>0) formData.append('immagine', file.files[0]);
    formData.append('specifiche', json_def);
    let url = `AdminServlet/modificaProdotto?marca=${marca}&modello=${modello}&prezzo=${prezzo}&descrizione=${descrizione}&dimensioni=${dimensioni}&peso=${peso}&categoria=${categoria}&id=${id_prodotto_global}`;
    //faccio una richiesta di tipo POST all'url creato passandogli il formData
    $.ajax({
        url: url,
        type:"POST",
        processData:false,
        contentType: false,
        data: formData,
        complete: function(data){
            alert("Prodotto modificato con successo!");
            window.location.replace("dashboard.jsp");
        }
    });
}

function riempiForm(jsonProdotto){
    $("#marca").val(jsonProdotto.marca);
    $("#modello").val(jsonProdotto.modello);
    $("#categorie").val(jsonProdotto.categoria);
    $("#prezzo").val(jsonProdotto.prezzo);
    $("#peso").val(jsonProdotto.peso);
    $("#dimensioni").val(jsonProdotto.dimensioni);
    $("#descrizione").val(jsonProdotto.descrizione);

    let specifiche = jsonProdotto.specifiche;
    for(i=0; i<specifiche.length; i++){
        let placeholder1 = "nome specifica " + (i);
        let placeholder2 = "valore specifica " + (i);
        let nome = specifiche[i].nome;
        let valore = specifiche[i].valore;
        $("#aggiuntaProdotto").find('tr:last').prev().prev().after('<tr class="specifica"> <td><input id="nome-specifica" type="text" value="'+nome+'" placeholder="'+placeholder1+'" required></td> <td><input id = "valore-specifica" type="text" value="'+valore+'" placeholder="'+placeholder2+'" required></td></tr>');
    }

}

$(document).ready(function (){
    $('html').css('cursor', 'wait');

    const queryString = window.location.search
    const urlParams = new URLSearchParams(queryString);
    const id_prodotto = urlParams.get('idProdotto');
    if(id_prodotto==null||id_prodotto==""){
        window.location.replace("WEB-INF/error-pages/notfound.jsp");
        return;
    }

    let xhttp = new XMLHttpRequest();
    xhttp.onreadystatechange = function() {
        if (this.readyState == 4 && this.status == 200) {
            $('html').css('cursor', 'default');
            riempiForm(JSON.parse(this.response));
        }
    };
    id_prodotto_global = id_prodotto;
    let url = "AdminServlet/getProdotto?idProdotto="+id_prodotto;
    xhttp.open("GET", url, true);
    xhttp.send();
});