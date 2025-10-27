<!DOCTYPE html>

<%@ page contentType="text/html; charset=UTF-8" pageEncoding="UTF-8" %>
<%@ taglib uri="http://java.sun.com/jsp/jstl/core" prefix="c" %>
<html lang="it">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <link rel="stylesheet" type="text/css" href="css/prodottoInfo.css">
    <link rel="stylesheet" type="text/css" href="./css/general.css">
    <link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/5.15.3/css/all.min.css">
    <title>${prodotto.marca} ${prodotto.modello} -2Chance</title>
</head>
<body>
<!-- MENU NAVIGAZIONALE -->
<div id="menu">
    <a href="landingpage"><img src="img/logo.png" alt="2Chance" id="logo"></a>
    <div id="searchbox">
        <form action="RicercaServlet" action="get" id="cerca">
            <i class="fas fa-search" onclick="document.getElementById('cerca').submit();"></i>
            <input type="text" name="val" id="cerca_input">
        </form>
    </div>
    <div id="navigazione">
        <c:choose>
            <c:when test="${sessionScope.user!= null}">
                <a href="paginaUtente.jsp" class="item-navigazione">${sessionScope.user.nome} <i class="fas fa-user-circle"></i></a>
            </c:when>
            <c:otherwise>
                <a href="login.jsp" class="item-navigazione">PROFILO <i class="fas fa-user-circle"></i></a>
            </c:otherwise>
        </c:choose>
        <a href="chiSiamo.jsp" class="item-navigazione">CHI SIAMO <i class="far fa-question-circle"></i></a>
        <c:choose>
            <c:when test="${sessionScope.user != null}">
                <a href="logoutServlet" class="item-navigazione">LOGOUT <i class="fas fa-sign-out-alt"></i></a>
            </c:when>
            <c:otherwise>
                <a href="login.jsp" class="item-navigazione">LOGIN <i class="fas fa-sign-in-alt"></i></a>
            </c:otherwise>
        </c:choose>
        <a href="carrello.jsp" class="item-navigazione">CARRELLO <i class="fas fa-shopping-cart"></i></a>
    </div>
    <i id="apri-mobile" class="fas fa-bars" onclick="mobileMenu('apri')"></i>
    <div id="navigazione-mobile">
        <i id="chiudi-mobile" class="fas fa-bars" onclick="mobileMenu('chiudi')"></i>
        <div id="items-mobile">
            <c:choose>
                <c:when test="${sessionScope.user != null}">
                    <a href="logoutServlet" class="item-navigazione">LOGOUT <i class="fas fa-sign-out-alt"></i></a>
                </c:when>
                <c:otherwise>
                    <a href="login.jsp" class="item-navigazione">LOGIN <i class="fas fa-sign-in-alt"></i></a>
                </c:otherwise>
            </c:choose>
            <a href="categorie.jsp" class="item-navigazione">CATALOGO <i class="fas fa-tags"></i></a>
            <a href="carrello.jsp" class="item-navigazione">CARRELLO <i class="fas fa-shopping-cart"></i></a>
            <a href="chiSiamo.jsp" class="item-navigazione">CHI SIAMO <i class="far fa-question-circle"></i></a>
            <c:choose>
                <c:when test="${sessionScope.user!= null}">
                    <a href="paginaUtente.jsp" class="item-navigazione">${sessionScope.user.nome} <i class="fas fa-user-circle"></i></a>
                </c:when>
                <c:otherwise>
                    <a href="login.jsp" class="item-navigazione">PROFILO <i class="fas fa-user-circle"></i></a>
                </c:otherwise>
            </c:choose>
        </div>
    </div>
</div>

<!-- FINE MENU NAVIGAZIONALE -->

<!-- CORPO PAGINA-->
<div id="corpo-pagina">
    <div id="prodotto">
        <div id="prodotto-copertina">
            <img src="${pageContext.request.contextPath}/img/${prodotto.immagine}" alt="">
        </div>
        <div id="prodotto-info">
            <p id="prodotto-nome">${prodotto.marca} ${prodotto.modello}</p>
            <p id="prodotto-prezzo">${prodotto.prezzo}€</p>
            <a href="AggiungiCarrelloServlet?prodotto=${prodotto.id}&quantita=1">
                <div class="prodotto-azioni">
                    <p>AGGIUNGI AL CARRELLO<i class="fas fa-shopping-cart"></i></p>
                </div>
            </a>
            <a href="WishlistServlet?cod=1&prodotto=${prodotto.id}">
                <div class="prodotto-azioni">
                    <p>AGGIUNGI ALLA WISHLIST<i class="fas fa-star"></i></p>
                </div>
            </a>
            <a href="#" onclick="confronta(${prodotto.id})">
                <div class="prodotto-azioni">
                    <p>CONFRONTA<i class="fas fa-not-equal"></i></p>
                </div>
            </a>
        </div>
    </div>
    <div id="info-box">
        <div id="info-box-controlli">
            <div class="pulsante-controlli pulsante-controlli-selezionato" onclick="show_box('descrizione', this)">
                <p>DESCRIZIONE</p>
            </div>
            <div class="pulsante-controlli" onclick="show_box('scheda-tecnica', this)">
                <p>SCHEDA TECNICA</p>
            </div>
            <div class="pulsante-controlli" onclick="show_box('recensioni', this)">
                <p>RECENSIONI</p>
            </div>
        </div>
        <div id="info-box-contenuto">
            <div id="descrizione" class="info-box-elemento info-box-elemento-selezionato">
                ${prodotto.descrizione}
            </div>
            <div id="scheda-tecnica" class="info-box-elemento">
                <table>
                    <tr>
                        <td class="nome-specifica">
                            dimensioni
                        </td>
                        <td class="valore-specifica">
                            ${prodotto.dimensioni}
                        </td>
                    </tr>
                    <tr>
                        <td class="nome-specifica">
                            peso
                        </td>
                        <td class="valore-specifica">
                            ${prodotto.peso} g
                        </td>
                    </tr>
                <c:forEach items="${prodotto.specifiche}" var="specifica">
                    <tr>
                        <td class="nome-specifica">
                            ${specifica.nome}
                        </td>
                        <td class="valore-specifica">
                            ${specifica.valore}
                        </td>
                    </tr>
                </c:forEach>
                </table>
            </div>
            <div id="recensioni" class="info-box-elemento">
                <table>
                    <c:forEach items="${prodotto.recensioni}" var="recensione">
                    <tr>
                        <td class="utente-recensione">
                            ${recensione.utente.nome}
                        </td>
                        <td class="valutazione-recensione">
                            <p>${recensione.valutazione}<i class="fas fa-star"></i></p>
                        </td>
                        <td class="testo-recensione">
                            <p>${recensione.testo}</p>
                        </td>
                        <td class="data-recensione">
                            <p>${recensione.dataRecensione}</p>
                        </td>
                    </tr>
                    </c:forEach>
                    <tr style="cursor: pointer">
                        <td id="scrivi-recensione" colspan="4" onclick="document.getElementById('nuovarecensione').classList.add('mostraAggiungiRecensione') ">
                            <p><i class="fas fa-pen-square"></i> recensisci questo prodotto!</p>
                        </td>
                    </tr>
                </table>
            </div>
        </div>
    </div>
</div>

<div id="nuovarecensione" class="">
    <div id="boxRecensione">
        <i class="fas fa-window-close" id="chiudi" onclick="document.getElementById('nuovarecensione').classList.remove('mostraAggiungiRecensione')"></i>
        <p>Recensione: </p><textarea name="testo" id="testo" style="font-size: 8px" rows="3"></textarea>
        <p>Valutazione: </p>
        <div id="stelle">
            <i class="fa fa-star stella-recensione yellow"></i><i class="fa fa-star stella-recensione"></i><i class="fa fa-star stella-recensione"></i><i class="fa fa-star stella-recensione"></i><i class="fa fa-star stella-recensione"></i>
        </div>
        <button onclick="aggiungiRecensione(${prodotto.id})" style="background-color: #F08354; color: white; padding: 3px; cursor: pointer; border: none">Invia</button>
    </div>
</div>
<!-- FINE CORPO PAGINA-->

<script src="https://ajax.googleapis.com/ajax/libs/jquery/3.6.0/jquery.min.js"></script>
<script src="functions/prodottoInfo.js"></script>
<script src="functions/general.js"></script>
</body>
</html>