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
    <link rel="stylesheet" type="text/css" href="${assetHost}/css/login.css" crossorigin="anonymous">
    <link rel="stylesheet" type="text/css" media="print" href="${assetHost}css/print.css" crossorigin="anonymous">
    <title>2Chance</title>

	<link rel="shortcut icon" href="${assetHost}favicon.ico" crossorigin="anonymous">
</head>
<body>

<div id="login-body">
    <a href="landingpage"><img src="${assetHost}img/logo.png" alt="2Chance Logo" id="logo" width="250" height="177" crossorigin="anonymous"></a>
    <!-- QUI VANNO TUTTI GLI ERRORI -->
    <c:forEach items="${errori}" var="errore">
        <p class="error">${errore}</p>
    </c:forEach>
    <!-- FIN QUI -->
    <form action="LoginServlet" method="post">
        <input type="email" name="email" placeholder="Inserisci la tua email" value="${email}" required>
        <input type="password" name="password" id="passwordInput" placeholder="Inserisci la tua password" onmouseover="show();" onmouseout="hide();" required>
        <input type="submit" value="Login">
    </form>
    <a href="registrazione.jsp" id="registrati">Registrati adesso</a>
</div>
<footer class="footer">
    <p>2Chance P.IVA: 12345577777777</p>
</footer>

<script src="${assetHost}/functions/login.js" crossorigin="anonymous"></script>
</body>
</html>