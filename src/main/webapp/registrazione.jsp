<!DOCTYPE html>
<%@ page contentType="text/html; charset=UTF-8" pageEncoding="UTF-8" %>
<%@ taglib uri="http://java.sun.com/jsp/jstl/core" prefix="c" %>
<html lang="it">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <link rel="stylesheet" type="text/css" href="./css/registrazione.css">
    <link rel="stylesheet" type="text/css" href="./css/general.css">
    <link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/5.15.3/css/all.min.css">
    <title>2Chance</title>
</head>
<body style="background-image: radial-gradient(circle, rgb(255,177,142) 0%, rgb(240,131,84) 100%);">

<div id="registrazione-body">
    <a href="landingpage"><img src="img/logocolorato.png" alt="" id="logo"></a>

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

<script src="https://ajax.googleapis.com/ajax/libs/jquery/3.6.0/jquery.min.js"></script>
<script src="./functions/registrazione.js"></script>
<script src="./functions/general.js"></script>
<style>
    .footer{
        color: white;
        background-color: #F08354;
        height: 2vh;
        text-align: center;
        width: 100%;
        text-align: center;
        position: fixed;
        left: 0;
        bottom: 0;
        display: flex;
        justify-content: center;
        align-items: center;
        font-size: 10px;
        z-index: 1000;
    }

    .footer p{
        margin: 0;
        padding: 0;
    }
</style>
</body>
</html>