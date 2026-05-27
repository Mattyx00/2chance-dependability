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
	<link rel="stylesheet" type="text/css" href="${assetHost}css/index.css" crossorigin="anonymous">
	<link rel="stylesheet" type="text/css" href="${assetHost}/css/general.css" crossorigin="anonymous">
	<link rel="stylesheet" type="text/css" media="print" href="${assetHost}css/print.css" crossorigin="anonymous">
	<link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/5.15.3/css/all.min.css">
 	<title>2Chance</title>
 
	<link rel="shortcut icon" href="${assetHost}favicon.ico" crossorigin="anonymous">
</head>
 <body onload="start()">
 <% if(session.getAttribute("user") != null){
	 if(((Utente) session.getAttribute("user")).isAdmin()) {
		 response.sendRedirect( request.getServletContext().getContextPath()+"/dashboard.jsp");
 }
 }%>
 	<!-- MENU NAVIGAZIONALE -->
 	<div id="menu">
 		<img src="${assetHost}img/logo.png" alt="2Chance" id="logo" crossorigin="anonymous">
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
 		<div id="menu-categorie">
 			<table>
 				<thead>
 					<tr>
 						<td>CATALOGO</td>
 					</tr>
 				</thead>
 				<tbody>
					<c:forEach items="${categorie}" var="cat">
						<tr>
							<td><a href="ProdottiPerCategoriaServlet?val=${cat.nomeCategoria}">${cat.nomeCategoria}<i class="fas fa-sort-down"></i></a></td>
						</tr>
					</c:forEach>

 				</tbody>
 			</table>
 		</div>
 		<div id="main-corpo">
 			<div id="carosello">
 				<img src="${assetHost}img/carosello1.webp" alt="" class="carosello-attiva" crossorigin="anonymous">
 				<img data-src="${assetHost}img/carosello2.webp" alt="" class="carosello-disattivata" crossorigin="anonymous">
 				<img data-src="${assetHost}img/carosello3.webp" alt="" class="carosello-disattivata" crossorigin="anonymous">
 				
 				<div id="carosello-cursori">
 					<i class="fas fa-chevron-left" onclick="cambiaFoto('precedente')"></i>
 					<i class="fas fa-chevron-right" onclick="cambiaFoto('successiva')"></i>
 				</div>
 			</div>
 			
 			<div id="prodotti-vetrina">

				<c:forEach items="${prodotti}" var="prodotto">
					<a href="ProdottoServlet?prodotto=${prodotto.id}">
						<div class="prodotto">
							<img src="${assetHost}img/${prodotto.immagineThumbnail}" alt="prodotto" class="immagine-prodotto" crossorigin="anonymous">
							<p class="titolo-prodotto">${prodotto.modello}</p>
							<p class="descrizione-prodotto">${prodotto.descrizione}</p>
							<p class="prezzo-prodotto">${prodotto.prezzo}€</p>
						</div>
					</a>
				</c:forEach>
 			</div>
 		</div>
 	</div>
 	<!-- FINE CORPO PAGINA-->
	<footer class="footer">
		<p>2Chance P.IVA: 12345577777777</p>
	</footer>

 	<script src="https://ajax.googleapis.com/ajax/libs/jquery/3.6.0/jquery.min.js" crossorigin="anonymous"></script>
 	<script src="${assetHost}functions/index.js" crossorigin="anonymous"></script>
	<script src="${assetHost}functions/general.js" crossorigin="anonymous"></script>
 </body>
 </html>