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
        <link rel="stylesheet" type="text/css" href="css/paginaUtente.css">
        <link rel="stylesheet" type="text/css" href="./css/general.css">
        <link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/5.15.3/css/all.min.css">
        <title>2Chance</title>
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
            <img id="pic-utente" style="margin-top: 10px" src="${pageContext.request.contextPath}/img/${sessionScope.user.immagine}" alt=""><i id="editImmagine" class="fas fa-pen-square"></i>
            <form id="formEditImmagine" action = 'EditProfiloServlet/editImmagine' enctype='multipart/form-data' method="post"><input type="file" name = "modifica" id="modificaImmagineInput" style="position: absolute; top:-150px"></form>
            <div id="nome-utente" style="display: flex; justify-content: center; align-items: center"><p id="nome">${sessionScope.user.nome}<i id="editNome" class="fas fa-pen-square"></i></p><p style="margin-left: 10px" id="cognome">${sessionScope.user.cognome}<i id="editCognome" class="fas fa-pen-square"></i></p></div>
            <p id="email">${sessionScope.user.email}<i id="editEmail" class="fas fa-pen-square"></i></p>
            <p id="telefono">${sessionScope.user.telefono}<i id="editTelefono" class="fas fa-pen-square"></i></p>
            <!-- <form action = EditProfiloServlet/editImmagine enctype='multipart/form-data' method="post"><input type="file" name = "modifica"><input type="submit"></form></p> -->
            <a href="WishlistServlet?cod=2" style="margin-bottom: 10px; margin-top: 10px; text-decoration: none; color: #F08354; font-size: 1.2em;"><i style="margin-right: 5px" class="fas fa-star"></i>WISHLIST</a>
            ORDINI
            <div id="ordini">
                <table>
                    <thead>
                        <tr>
                            <td>DATA ORDINE</td>
                            <td>INDIRIZZO</td>
                            <td>TOTALE</td>
                            <td></td>
                        </tr>
                    </thead>
                    <tbody>
                         <% int x = 0;
                             request.setAttribute("cod", x);%>

                         <c:forEach items="${sessionScope.user.ordini}" var="ordine">

                            <tr>
                                <td>${ordine.dataOrdine}</td>
                                <td>${ordine.indirizzo}</td>
                                <td>${ordine.prezzoTotale}</td>

                                <td><a href="visualizzaOrdine.jsp?idOrdine=${ordine.id}&cod=${requestScope.cod}">Visualizza Info Ordine</a></td>
                            </tr>
                             <%x = x+1;
                                 request.setAttribute("cod", x);%>

                        </c:forEach>
                    </tbody>
                </table>
            </div>
           <br>
            RECENSIONI

            <div id="recensioni">
                <table>
                    <thead>
                    <tr>
                        <td>DATA RECENSIONE</td>
                        <td>PRODOTTO</td>
                        <td>TESTO</td>
                        <td>VALUTAZIONE</td>
                        <td></td>
                    </tr>
                    </thead>
                    <tbody>
                    <c:forEach items="${sessionScope.user.recensioni}" var="recensione">
                        <tr>
                            <td>${recensione.dataRecensione}</td>
                            <td>${recensione.prodotto.marca} ${recensione.prodotto.modello}</td>
                            <td>${recensione.testo}</td>
                            <td>${recensione.valutazione}</td>
                            <td><a href="RecensioniServlet/eliminaRecensione?recensione=${recensione.id}">Elimina Recensione</a></td>
                        </tr>
                    </c:forEach>
                    </tbody>
                </table>
            </div>
        </div>
        <!-- FINE CORPO PAGINA-->
        <footer class="footer">
            <p>2Chance P.IVA: 12345577777777</p>
        </footer>
    <script src="https://ajax.googleapis.com/ajax/libs/jquery/3.6.0/jquery.min.js"></script>
        <script src="functions/registrazione.js"></script>
    <script src="functions/paginaUtente.js"></script>
    <script src="functions/general.js"></script>
    </body>
</html>