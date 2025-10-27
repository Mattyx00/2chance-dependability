function mobileMenu(azione){
    if(azione=="apri"){
        $(`#navigazione-mobile`).css("left", "0px");
    }else{
        $(`#navigazione-mobile`).css("left", "-45vw");
    }
}

$(window).scroll(function() { //SERVE A CHIUDERE IL MENU QUANDO L'UTENTE COMINCIA A SCORRERE LA PAGINA
    var scrollTop = $(window).scrollTop();
    if ( scrollTop > 0 ) {
        mobileMenu("chiudi");
    }
});