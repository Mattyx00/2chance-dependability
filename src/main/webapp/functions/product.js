function abbreviaDesc(){
    let descrizioni = document.getElementsByClassName("descrizione-prodotto")
    for(i=0; i<descrizioni.length; i++){
        let testo = descrizioni[i].innerHTML;
        if(testo.length>20) descrizioni[i].innerHTML = testo.substring(0, 20) + "...";

    }

    let titolo = document.getElementsByClassName("titolo-prodotto")
    for(i=0; i<titolo.length; i++){
        let testo = titolo[i].innerHTML;
        if(testo.length>15) titolo[i].innerHTML = testo.substring(0, 15) + "...";
    }
}

function setSearchBar(){
    const urlParams = new URLSearchParams(window.location.search);
    const categoria = urlParams.get('val');
    document.getElementById("cerca_input").value = categoria;
}

function start(){
    abbreviaDesc();
    setSearchBar();
}