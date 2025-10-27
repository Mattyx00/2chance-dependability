<%@ page import="model.beans.Utente" %>
<%@ page import="model.beans.Ordine" %>
<%@ page import="java.util.ArrayList" %>
<!DOCTYPE html>

<%@ page contentType="text/html; charset=UTF-8" pageEncoding="UTF-8" %>
<%@ taglib uri="http://java.sun.com/jsp/jstl/core" prefix="c" %>
<html lang="it">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <link rel="stylesheet" type="text/css" href="css/aggiungiProdotto.css">
    <link rel="stylesheet" type="text/css" href="./css/general.css">
    <link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/5.15.3/css/all.min.css">
    <title>Modifica Prodotto - 2Chance</title>
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
                <a href="#" class="item-navigazione">${sessionScope.user.nome} <i class="fas fa-user-circle"></i></a>
            </c:when>
            <c:otherwise>
                <a href="#" class="item-navigazione">PROFILO <i class="fas fa-user-circle"></i></a>
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
                    <a href="#" class="item-navigazione">${sessionScope.user.nome} <i class="fas fa-user-circle"></i></a>
                </c:when>
                <c:otherwise>
                    <a href="#" class="item-navigazione">PROFILO <i class="fas fa-user-circle"></i></a>
                </c:otherwise>
            </c:choose>
        </div>
    </div>
</div>
<!-- FINE MENU NAVIGAZIONALE -->

<!-- CORPO PAGINA-->
<div id="corpo-pagina">
    <table id="aggiuntaProdotto">
        <tr>
            <td>marca</td>
            <td><input type="text" name="marca" id="marca" required></td>
        </tr>
        <tr>
            <td>modello</td>
            <td><input type="text" name="modello" id="modello" required></td>
        </tr>
        <tr>
            <td>categoria</td>
            <td><select name="categorie" name="categoria" id="categorie" required></select></td> <!--RICORDA DI RIEMPIRLE CON JQUERY -->
        </tr>
        <tr>
            <td>prezzo</td>
            <td><input type="number" name="prezzo" id="prezzo" min="0.01" step=".01" required></td>
        </tr>
        <tr>
            <td>peso</td>
            <td><input type="number" name="peso" id="peso" min="0.01" step=".1" required></td>
        </tr>
        <tr>
            <td>dimensioni</td>
            <td><input type="text" name="dimensioni" id="dimensioni" required></td>
        </tr>
        <tr>
            <td>descrizione</td>
            <td><textarea rows="3" name="descrizione" id="descrizione" required></textarea></td>
        </tr>
        <tr>
            <td colspan="2"><input type="file" name="immagine" id="immagine"></td>
        </tr>
        <tr>
            <td colspan="2"><button style="width: 100%" onclick="nuovaRiga()">Aggiungi Specifica</button></td>
        </tr>
        <tr>
            <td colspan="2"><button style="width: 100%" onclick="salvaModificaProdotto()">Salva</button></td>
        </tr>
    </table>
</div>
<!-- FINE CORPO PAGINA-->
<script src="https://ajax.googleapis.com/ajax/libs/jquery/3.6.0/jquery.min.js"></script>
<script src="functions/aggiungiProdotto.js"></script>
<script src="functions/modificaProdotto.js"></script>
<script src="functions/general.js"></script>
</body>
</html>