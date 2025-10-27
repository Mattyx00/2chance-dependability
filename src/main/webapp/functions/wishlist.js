function eliminaProdottoWishList(idprodotto, idutente){
    let xhttp = new XMLHttpRequest();
    xhttp.onreadystatechange = function() {
        if (this.readyState == 4 && this.status == 200) {
            location.reload();
        }
    };
    let url = "WishlistServlet?cod=3" + "&id_utente="+ idutente + "&id_prodotto="+idprodotto;
    xhttp.open("GET", url, true);
    xhttp.send();
}

