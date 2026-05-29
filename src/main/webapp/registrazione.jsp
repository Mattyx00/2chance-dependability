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
    <link rel="stylesheet" type="text/css" href="${assetHost}/css/registrazione.css" crossorigin="anonymous">
    <link rel="stylesheet" type="text/css" media="print" href="${assetHost}css/print.css" crossorigin="anonymous">
    <title>2Chance</title>

	<link rel="shortcut icon" href="${assetHost}favicon.ico" crossorigin="anonymous">
</head>
<body>

<div id="registrazione-body">
    <a href="landingpage"><img src="${assetHost}img/logo.png" alt="2Chance Logo" id="logo" width="250" height="177" crossorigin="anonymous"></a>

    <!-- QUI VANNO TUTTI GLI ERRORI -->
    <c:forEach items="${errori}" var="errore">
        <p class="error">${errore}</p>
    </c:forEach>
    <!-- FIN QUI -->
    <!-- valido i dati inseriti dall'utente in onSubmit con la funzione controllaCampi() -->
    <form enctype="multipart/form-data" action="RegistrazioneServlet" method="post" onsubmit="return controllaCampi()" name="registrazione">
        <input type="email" name="email" placeholder="Inserisci la tua email" value="${email}" required>
        <input type="text" name="nome" placeholder="Inserisci il tuo nome" value="${nome}" required>
        <input type="text" name="cognome" placeholder="Inserisci il tuo cognome" value="${cognome}" required>
        <input type="tel" name="telefono" placeholder="Inserisci il tuo cellulare es: 1234567890" value="${telefono}"required>
        <input type="file" name="file" placeholder="Inserisci un immagine" >
        <input type="password" name="password" id="passwordInput" placeholder="Inserisci la tua password" onmouseover="show();" onmouseout="hide();" required>
        <input type="submit" value="Registrati">
    </form>
</div>

<footer class="footer">
    <p>2Chance P.IVA: 12345577777777</p>
</footer>

<script src="${assetHost}/functions/registrazione.js" crossorigin="anonymous"></script>
</body>
</html>