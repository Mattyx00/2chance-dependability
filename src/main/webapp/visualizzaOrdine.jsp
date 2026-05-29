<%@ page import="model.beans.Utente" %>
<!DOCTYPE html>

<%@ page contentType="text/html; charset=UTF-8" pageEncoding="UTF-8" %>
<%@ taglib uri="http://java.sun.com/jsp/jstl/core" prefix="c" %>
<html lang="it">
<head>
<%
    String serverName = request.getServerName();
    int port = request.getServerPort();
    String assetHost;
    if ("localhost".equalsIgnoreCase(serverName)) {
        assetHost = "http://127.0.0.1:" + port + request.getContextPath() + "/";
    } else if ("127.0.0.1".equals(serverName)) {
        assetHost = "http://localhost:" + port + request.getContextPath() + "/";
    } else {
        assetHost = request.getContextPath() + "/";
    }
    pageContext.setAttribute("assetHost", assetHost);
%>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <link rel="stylesheet" type="text/css" href="${assetHost}css/carrello.css" crossorigin="anonymous">
    <link rel="stylesheet" type="text/css" href="${assetHost}css/visualizzaOrdine.css" crossorigin="anonymous">
    <link rel="stylesheet" type="text/css" href="${assetHost}/css/general.css" crossorigin="anonymous">
    <link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/5.15.3/css/all.min.css">
    <title>Visualizza ordine - 2Chance</title>

	<link rel="shortcut icon" href="${assetHost}favicon.ico" crossorigin="anonymous">

	<link rel="stylesheet" type="text/css" media="print" href="${assetHost}css/print.css" crossorigin="anonymous">
</head>
<body>
<!-- MENU NAVIGAZIONALE -->
<div id="menu">
    <a href="landingpage"><img src="${assetHost}img/logo.png" alt="2Chance" id="logo" crossorigin="anonymous"></a>
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
    <h2>Ordine</h2>
    <div id="corpo-carrello">

        <%int cod = Integer.parseInt(request.getParameter("cod"));
            request.setAttribute("index", cod);%>
        <c:forEach items="${sessionScope.user.ordini[requestScope.index].carrello.prodotti}" var="prodotto">
            <div class="prodottoCarrello">
                <img src="${assetHost}img/${prodotto.prodotto.immagineThumbnail}" alt="" class="immagineProdottoCarrello" crossorigin="anonymous">
                <a href="ProdottoServlet?prodotto=${prodotto.prodotto.id}" class="infoProdottoCarrello" style="text-decoration: none; color: inherit;">
                    <p class="nomeProdottoCarrello">${prodotto.prodotto.marca} ${prodotto.prodotto.modello}</p>
                    <p class="prezzoProdottoCarrello">${prodotto.prodotto.prezzo}€</p>
                </a>
                <p>Quantita: ${prodotto.quantita}</p>
            </div>

        </c:forEach>
    </div>

</div>
<!-- FINE CORPO PAGINA-->

<script src="${assetHost}functions/general.js" crossorigin="anonymous"></script>

</body>
</html>
