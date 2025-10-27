<%@ page import="model.beans.Utente" %>
<!DOCTYPE html>

<%@ page contentType="text/html; charset=UTF-8" pageEncoding="UTF-8" %>
<%@ taglib uri="http://java.sun.com/jsp/jstl/core" prefix="c" %>
<html lang="it">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <link rel="stylesheet" type="text/css" href="./css/index.css">
    <link rel="stylesheet" type="text/css" href="./css/general.css">
    <link rel="stylesheet" type="text/css" href="./css/dashboard.css">
    <link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/5.15.3/css/all.min.css">
    <!---DATATABLE E BOOTSTRAP -->
    <script src="https://ajax.googleapis.com/ajax/libs/jquery/3.6.0/jquery.min.js"></script>
    <link rel="stylesheet" href="https://cdn.datatables.net/1.10.25/css/dataTables.bootstrap5.min.css">
    <link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/twitter-bootstrap/5.0.1/css/bootstrap.min.css">
    <script type="text/javascript" charset="utf8" src="https://cdn.datatables.net/1.10.25/js/jquery.dataTables.js"></script>
    <script src="https://cdn.datatables.net/1.10.25/js/dataTables.bootstrap5.min.js"></script>
    <script src="https://cdn.jsdelivr.net/npm/bootstrap@5.0.2/dist/js/bootstrap.bundle.min.js" integrity="sha384-MrcW6ZMFYlzcLA8Nl+NtUVF0sA7MsXsP1UyJoMp4YLEuNSfAP+JcXn/tWtIaxVXM" crossorigin="anonymous"></script>
    <script src="https://cdn.datatables.net/buttons/1.7.1/js/dataTables.buttons.min.js"></script>
    <title>2Chance</title>
</head>
<body>
<%Utente u = (Utente) session.getAttribute("user");
    if(u == null || !u.isAdmin()) {
        response.sendError(HttpServletResponse.SC_UNAUTHORIZED);
    }
%>
<!-- MENU NAVIGAZIONALE -->
<div id="menu">
    <img src="img/logo.png" alt="2Chance" id="logo">
    <div id="searchbox">
        <form action="RicercaServlet" action="get" id="cerca">
            <i class="fas fa-search" onclick="document.getElementById('cerca').submit();"></i>
            <input type="text" name="val" id="cerca_input">
        </form>
    </div>
    <div id="navigazione">
        <c:choose>
            <c:when test="${sessionScope.user!= null}">
                <a class="item-navigazione">bentornato admin <i class="fas fa-user-circle"></i></a>
            </c:when>
            <c:otherwise>
                <a href="login.jsp" class="item-navigazione">PROFILO <i class="fas fa-user-circle"></i></a>
            </c:otherwise>
        </c:choose>

        <c:choose>
            <c:when test="${sessionScope.user != null}">
                <a href="logoutServlet" class="item-navigazione">LOGOUT <i class="fas fa-sign-out-alt"></i></a>
            </c:when>
            <c:otherwise>
                <a href="login.jsp" class="item-navigazione">LOGIN <i class="fas fa-sign-in-alt"></i></a>
            </c:otherwise>
        </c:choose>

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
            <c:choose>
                <c:when test="${sessionScope.user!= null}">
                    <a href="paginaUtente.jsp" class="item-navigazione">${sessionScope.user.nome} <i class="fas fa-user-circle"></i></a>
                </c:when>
                <c:otherwise>
                    <a href="login.jsp" class="item-navigazione">PROFILO <i class="fas fa-user-circle"></i></a>
                </c:otherwise>
            </c:choose>
            <p class="item-navigazione" onclick="show('prodotti')">Gestione Prodotti</p>
            <p class="item-navigazione" onclick="show('categorie')">Gestione Categorie</p>
            <p class="item-navigazione" onclick="show('utenti')">Mostra Utenti</p>
            <p class="item-navigazione" onclick="show('ordini')">Mostra Ordini</p>
        </div>
    </div>
</div>
<!-- FINE MENU NAVIGAZIONALE -->

<div id="corpo-pagina">
    <div id="menu-categorie">
        <table>
            <thead>
            <tr>
                <td>GESTIONE</td>
            </tr>
            </thead>
            <tbody>
                <tr onclick="show('prodotti')">
                    <td>Gestione Prodotti<i class="fas fa-sort-down"></i></td>
                </tr>
                <tr onclick="show('categorie')">
                    <td>Gestione Categorie<i class="fas fa-sort-down"></i></td>
                </tr>
                <tr onclick="show('utenti')">
                    <td>Mostra Utenti<i class="fas fa-sort-down"></i></td>
                </tr>
                <tr onclick="show('ordini')">
                    <td>Mostra Ordini<i class="fas fa-sort-down"></i></td>
                </tr>
            </tbody>
        </table>
    </div>
    <div id="main-corpo">
        <div id="datagrid_visualizzaprodotti" class="datagrid_centrali hide">
            <table id="tabella_prodotti"  class="table table-hover ">
                <thead>
                <tr>
                    <th>id</th>
                    <th>marca</th>
                    <th>modello</th>
                    <th>categoria</th>
                    <th>prezzo</th>
                    <th>elimina</th>
                    <th>modifica</th>
                </tr>
                </thead>
                <tbody>
                </tbody>
            </table>
        </div>
        <div id="datagrid_visualizzacategorie" class="datagrid_centrali hide">
            <table id="tabella_categorie"  class="table table-hover ">
                <thead>
                <tr>
                    <th>categoria</th>
                    <th>elimina</th>
                </tr>
                </thead>
                <tbody>
                </tbody>
            </table>
        </div>
        <div id="datagrid_visualizzautenti" class="datagrid_centrali hide">
            <table id="tabella_utenti"  class="table table-hover ">
                <thead>
                <tr>
                    <th>id</th>
                    <th>nome</th>
                    <th>cognome</th>
                    <th>email</th>
                    <th>telefono</th>
                </tr>
                </thead>
                <tbody>
                </tbody>
            </table>
        </div>
        <div id="datagrid_visualizzaordini" class="datagrid_centrali hide">
            <table id="tabella_ordini"  class="table table-hover ">
                <thead>
                <tr>
                    <th>id</th>
                    <th>utente</th>
                    <th>data</th>
                    <th>indirizzo</th>
                    <th>totale</th>
                    <th>info</th>
                </tr>
                </thead>
                <tbody>
                </tbody>
            </table>
        </div>
    </div>

</div>

<footer class="footer">
    <p>2Chance P.IVA: 12345577777777</p>
</footer>

<script src="functions/index.js"></script>
<script src="functions/general.js"></script>
<script src="functions/dashboard.js"></script>


</body>
</html>