<!DOCTYPE html>

<%@ page contentType="text/html; charset=UTF-8" pageEncoding="UTF-8" %>
<%@ taglib uri="http://java.sun.com/jsp/jstl/core" prefix="c" %>
<html lang="it">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <link rel="stylesheet" type="text/css" href="css/carrello.css">
    <link rel="stylesheet" type="text/css" href="./css/general.css">
    <link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/5.15.3/css/all.min.css">
    <title>Carrello - 2Chance</title>
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
    <div id="corpo-carrello">
        <c:forEach items="${sessionScope.carrello.prodotti}" var="prodotto">
            <div class="prodottoCarrello">
                <img src="${pageContext.request.contextPath}/img/${prodotto.prodotto.immagine}" alt="" class="immagineProdottoCarrello">
                <a href="ProdottoServlet?prodotto=${prodotto.prodotto.id}">
                <div class="infoProdottoCarrello">
                    <p class="nomeProdottoCarrello">${prodotto.prodotto.marca} ${prodotto.prodotto.modello}</p>
                    <p class="prezzoProdottoCarrello">${prodotto.prodotto.prezzo}€</p>
                </div>
                </a>
                <input prodotto="${prodotto.prodotto.id} "type="number" class="quantitaProdottoCarrello" min="1" step="1" value="${prodotto.quantita}">
                <i class="fas fa-trash-alt eliminaProdottoCarrello" onclick="eliminaProdotto(${prodotto.prodotto.id})"></i>
            </div>
        </c:forEach>
    </div>
    <form action = CheckOutServlet id="formAcquista" onsubmit="acquista()">
        <input type="hidden" id="indirizzo" value="" name="indirizzo">
        <input type="submit" value="ACQUISTA" id ="acquistaCarrello">
    </form>

</div>
<!-- FINE CORPO PAGINA-->

<footer class="footer">
    <p>2Chance P.IVA: 12345577777777</p>
</footer>
<script src="https://ajax.googleapis.com/ajax/libs/jquery/3.6.0/jquery.min.js"></script>
<script src="functions/carrello.js"></script>
<script src="functions/general.js"></script>

</body>
</html>