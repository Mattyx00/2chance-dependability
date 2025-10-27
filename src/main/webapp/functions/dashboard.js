function eliminaProdotto(id){
    let xhttp = new XMLHttpRequest();
    xhttp.onreadystatechange = function() {
        if (this.readyState == 4 && this.status == 200) {
            alert("Prodotto eliminato con successo!");
            location.reload();
        }
    };
    let url = "AdminServlet/eliminaProdotto?id="+id;
    xhttp.open("GET", url, true);
    xhttp.send();
}

function eliminaCategoria(categoria){
    let xhttp = new XMLHttpRequest();
    xhttp.onreadystatechange = function() {
        if (this.readyState == 4 && this.status == 200) {
            alert("Categoria eliminata con successo!");
            location.reload();
        }
    };
    let url = "AdminServlet/eliminaCategoria?nomeCategoria="+categoria;
    xhttp.open("GET", url, true);
    xhttp.send();
}

function modificaProdotto(id){
    window.location.href = "modificaProdotto.jsp?idProdotto="+id;
}

function infoOrdine(id_ordine){
    window.location.href = ("visualizzaOrdineAdmin.jsp?ordine="+id_ordine);
}

function aggiungiCategoria(){
    let categoria = prompt("Inserisci la nuova categoria: ");
    if(categoria==null||categoria=="") return;
    let xhttp = new XMLHttpRequest();
    xhttp.onreadystatechange = function() {
        if (this.readyState == 4 && this.status == 200) {
            alert("Categoria aggiunta con successo!");
            location.reload();
        }
    };
    let url = "AdminServlet/aggiungiCategoria?nomeCategoria="+categoria;
    xhttp.open("GET", url, true);
    xhttp.send();
}

function aggiungiProdotto(){
    window.location.href = "aggiuntaProdotto.jsp";
}

table_prodotti = null;
function loadTableProdotti(jsonProdotti){
    if(table_prodotti != null) return;
    table_prodotti = $('#tabella_prodotti').DataTable({
        "dom": '<"toolbar">frtip',
        "scrollY": "60vh",
        "scrollCollapse": true,
        'language': {
            "decimal": "",
            "emptyTable": "Nessun prodotto presente",
            "info": " _TOTAL_ prodotti",
            "infoEmpty": "Mostrando da 0 a 0 di 0 prodotti",
            "infoFiltered": "(filtrato da _MAX_ prodotti totali)",
            "infoPostFix": "",
            "thousands": ",",
            "lengthMenu": "Mostra _MENU_ prodotti",
            "loadingRecords": "Caricando...",
            "processing": "Processando...",
            "search": "Cerca:",
            "zeroRecords": "Nessun prodotto trovato!",
            "paginate": {
                "first": "Prima",
                "last": "Ultima",
                "next": "Prossima",
                "previous": "Precedente"
            },
            "aria": {
                "sortAscending": ": attiva per ordinare le colonne in ordine crescente",
                "sortDescending": ": attiva per ordinare le colonne in ordine decrescente"
            }
        },
        "data": jsonProdotti.prodotti,
        "columns": [
            {"data": "id"},
            {"data": "marca"},
            {"data": "modello"},
            {"data": "categoria"},
            {"data": "prezzo"},
            {"data": "<button class=\"btn\"><i class=\"fa fa-trash-alt\"></i></button>"},
            {"data": "<button class=\"btn\"><i class=\"fas fa-pen\"></i></button>"}
        ],
        columnDefs: [
            {
                "targets": -2,
                "data": null,
                "defaultContent": '<button id="cancella" style="background-color: #F08354; border: none; color: white; padding: 12px 16px; font-size: 16px; cursor: pointer;"><i id="elimina_icon" class="fas fa-trash-alt"></i></button>'
            },
            {
                "targets": -1,
                "data": null,
                "defaultContent": '<button id="modifica" style="background-color: #F08354; border: none; color: white; padding: 12px 16px; font-size: 16px; cursor: pointer;"><i id="modifica_icon" class="fas fa-pen"></i></button>'
            }
        ]
    });
    //aggiungo pulsante [+] aggiungi prodotto
    $("#datagrid_visualizzaprodotti div.toolbar").html('<button onclick="aggiungiProdotto()" style="font-size: 15px; color: white; background-color: #F08354; border: none; cursor: pointer"><i style="padding: 10px" class="fas fa-plus"></i></button>');


    //creo listener per il click dei pulsanti "cancella" e "modifica"
    $('#tabella_prodotti tbody').on('click', 'tr', function (e) {
        if(e.target.getAttribute("id")=="modifica"||e.target.getAttribute("id")=="modifica_icon"){
            if (e.target.nodeName == 'BUTTON' || e.target.nodeName == 'I') {
                let id_prodotto = table_prodotti.row( this ).data().id;
                modificaProdotto(id_prodotto);
            }
        }else{
            if(e.target.getAttribute("id")=="cancella"||e.target.getAttribute("id")=="elimina_icon"){
                if (e.target.nodeName == 'BUTTON' || e.target.nodeName == 'I') {
                    let id_prodotto = table_prodotti.row( this ).data().id;
                    eliminaProdotto(id_prodotto);
                }
            }
        }

    });
}

table_categorie = null;
function loadTableCategorie(jsonCategorie){

    jsonCategorie = jsonCategorie.categorie;
    jsonCategorie_provv = new Array();
    for(i=0; i<jsonCategorie.length; i++){
        jsonCategorie_provv.push(new Array(jsonCategorie[i]));
    }
    jsonCategorie = jsonCategorie_provv;
    if(table_categorie != null) return;
    table_categorie = $('#tabella_categorie').DataTable({
        "dom": '<"toolbar">frtip',
        "scrollY": "60vh",
        "scrollCollapse": true,
        'language': {
            "decimal": "",
            "emptyTable": "Nessuna categoria presente",
            "info": " _TOTAL_ categorie",
            "infoEmpty": "Mostrando da 0 a 0 di 0 categorie",
            "infoFiltered": "(filtrato da _MAX_ categorie totali)",
            "infoPostFix": "",
            "thousands": ",",
            "lengthMenu": "Mostra _MENU_ categorie",
            "loadingRecords": "Caricando...",
            "processing": "Processando...",
            "search": "Cerca:",
            "zeroRecords": "Nessuna categoria trovato!",
            "paginate": {
                "first": "Prima",
                "last": "Ultima",
                "next": "Prossima",
                "previous": "Precedente"
            },
            "aria": {
                "sortAscending": ": attiva per ordinare le colonne in ordine crescente",
                "sortDescending": ": attiva per ordinare le colonne in ordine decrescente"
            }
        },
        "data": jsonCategorie,
        "columns": [
            {"title": "Nome"},
            {"data": "<button class=\"btn\"><i class=\"fa fa-trash-alt\"></i></button>"}
        ],
        columnDefs: [
            {
                "targets": -1,
                "data": null,
                "defaultContent": '<button id="cancella" style="background-color: #F08354; border: none; color: white; padding: 12px 16px; font-size: 16px; cursor: pointer;"><i id="elimina_icon" class="fas fa-trash-alt"></i></button>'
            }
        ]
    });
    $("#datagrid_visualizzacategorie div.toolbar").html('<button onclick="aggiungiCategoria()" style="font-size: 15px; color: white; background-color: #F08354; border: none; cursor: pointer"><i style="padding: 10px" class="fas fa-plus"></i></button>');

    $('#tabella_categorie tbody').on('click', 'tr', function (e) {
        if(e.target.getAttribute("id")=="cancella"||e.target.getAttribute("id")=="elimina_icon"){
            if (e.target.nodeName == 'BUTTON' || e.target.nodeName == 'I') {
                let categoria = table_categorie.row( this ).data();
                eliminaCategoria(categoria);
            }
        }
    });
}

table_utenti = null;
function loadTableUtenti(jsonUtenti){
    if(table_utenti != null) return;
    table_utenti = $('#tabella_utenti').DataTable({
        "scrollY": "60vh",
        "scrollCollapse": true,
        'language': {
            "decimal": "",
            "emptyTable": "Nessun utente presente",
            "info": " _TOTAL_ utenti",
            "infoEmpty": "Mostrando da 0 a 0 di 0 utenti",
            "infoFiltered": "(filtrato da _MAX_ prodotti totali)",
            "infoPostFix": "",
            "thousands": ",",
            "lengthMenu": "Mostra _MENU_ utenti",
            "loadingRecords": "Caricando...",
            "processing": "Processando...",
            "search": "Cerca:",
            "zeroRecords": "Nessun utente trovato!",
            "paginate": {
                "first": "Prima",
                "last": "Ultima",
                "next": "Prossima",
                "previous": "Precedente"
            },
            "aria": {
                "sortAscending": ": attiva per ordinare le colonne in ordine crescente",
                "sortDescending": ": attiva per ordinare le colonne in ordine decrescente"
            }
        },
        "data": jsonUtenti.utenti,
        "columns": [
            {"data": "id"},
            {"data": "nome"},
            {"data": "cognome"},
            {"data": "email"},
            {"data": "telefono"}
        ]
    });
}

table_ordini = null;
function loadTableOrdini(jsonOrdini){
    console.log(jsonOrdini);
    if(table_ordini != null) return;
    table_ordini = $('#tabella_ordini').DataTable({
        "scrollY": "60vh",
        "scrollCollapse": true,
        'language': {
            "decimal": "",
            "emptyTable": "Nessun ordine presente",
            "info": " _TOTAL_ ordini",
            "infoEmpty": "Mostrando da 0 a 0 di 0 ordini",
            "infoFiltered": "(filtrato da _MAX_ ordini totali)",
            "infoPostFix": "",
            "thousands": ",",
            "lengthMenu": "Mostra _MENU_ ordini",
            "loadingRecords": "Caricando...",
            "processing": "Processando...",
            "search": "Cerca:",
            "zeroRecords": "Nessun ordine trovato!",
            "paginate": {
                "first": "Prima",
                "last": "Ultima",
                "next": "Prossima",
                "previous": "Precedente"
            },
            "aria": {
                "sortAscending": ": attiva per ordinare le colonne in ordine crescente",
                "sortDescending": ": attiva per ordinare le colonne in ordine decrescente"
            }
        },
        "data": jsonOrdini.ordini,
        "columns": [
            {"data": "id"},
            {"data": "utente"},
            {"data": "data"},
            {"data": "indirizzo"},
            {"data": "totale"},
            {"data": "<button class=\"btn\"><i class=\"fa fa-info\"></i></button>"}
        ],
        columnDefs: [
            {
                "targets": -1,
                "data": null,
                "defaultContent": '<button id="info" style="background-color: #F08354; border: none; color: white; padding: 12px 16px; font-size: 16px; cursor: pointer;"><i id="info_icon" class="fas fa-info"></i></button>'
            }
        ]
    });

    $('#tabella_ordini tbody').on('click', 'tr', function (e) {
        if(e.target.getAttribute("id")=="info"||e.target.getAttribute("id")=="info_icon"){
            if (e.target.nodeName == 'BUTTON' || e.target.nodeName == 'I') {
                let id_ordine = table_ordini.row( this ).data().id;
                infoOrdine(id_ordine);
            }
        }
    });

}


function show(element){
    //elimino la classe "show" (quindi nascondendola) alla tabella dei prodotti, categorie, utenti e ordini
    $("#datagrid_visualizzaprodotti").removeClass("show");
    $("#datagrid_visualizzacategorie").removeClass("show");
    $("#datagrid_visualizzautenti").removeClass("show");
    $("#datagrid_visualizzaordini").removeClass("show");

    if(element=="prodotti"){
        let xhttp = new XMLHttpRequest();
        xhttp.onreadystatechange = function() {
            if (this.readyState == 4 && this.status == 200) {
                console.log(this.response);
                loadTableProdotti(JSON.parse(this.response));
            }
        };
        let url = "AdminServlet/mostraProdotti";
        xhttp.open("GET", url, true);
        xhttp.send();
        $("#datagrid_visualizzaprodotti").addClass("show");
        return;
    }

    if(element=="categorie"){
        let xhttp = new XMLHttpRequest();
        xhttp.onreadystatechange = function() {
            if (this.readyState == 4 && this.status == 200) {
                loadTableCategorie(JSON.parse(this.response));
            }
        };
        let url = "AdminServlet/mostraCategorie";
        xhttp.open("GET", url, true);
        xhttp.send();
        $("#datagrid_visualizzacategorie").addClass("show");
        return;
    }

    if(element=="utenti"){
        let xhttp = new XMLHttpRequest();
        xhttp.onreadystatechange = function() {
            if (this.readyState == 4 && this.status == 200) {
                loadTableUtenti(JSON.parse(this.response));
            }
        };
        let url = "AdminServlet/mostraUtenti";
        xhttp.open("GET", url, true);
        xhttp.send();
        $("#datagrid_visualizzautenti").addClass("show");
        return;
    }

    if(element=="ordini"){
        let xhttp = new XMLHttpRequest();
        xhttp.onreadystatechange = function() {
            if (this.readyState == 4 && this.status == 200) {
                loadTableOrdini(JSON.parse(this.response));
            }
        };
        let url = "AdminServlet/mostraOrdini";
        xhttp.open("GET", url, true);
        xhttp.send();
        $("#datagrid_visualizzaordini").addClass("show");
        return;
    }
}