function mobileMenu(azione){
    if(azione=="apri"){
        document.getElementById('navigazione-mobile').style.left = "0px";
    }else{
        document.getElementById('navigazione-mobile').style.left = "-45vw";
    }
}

window.addEventListener('scroll', function() { //SERVE A CHIUDERE IL MENU QUANDO L'UTENTE COMINCIA A SCORRERE LA PAGINA
    var scrollTop = window.pageYOffset || document.documentElement.scrollTop;
    if ( scrollTop > 0 ) {
        mobileMenu("chiudi");
    }
});