<%@ page import="model.beans.Utente" %>
<!DOCTYPE html>
<%@ page contentType="text/html; charset=UTF-8" pageEncoding="UTF-8" %>
<%@ taglib uri="http://java.sun.com/jsp/jstl/core" prefix="c" %>
<html lang="it">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <link rel="stylesheet" type="text/css" href="css/index.css">
    <link rel="stylesheet" type="text/css" href="./css/general.css">
    <link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/5.15.3/css/all.min.css">
    <title>Chi siamo - 2Chance</title>
</head>
<body onload="start()">
<!-- MENU NAVIGAZIONALE -->
<div id="menu">
    <a href="index.jsp"><img src="img/logo.png" alt="2Chance" id="logo"></a>
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
        <a href="#" class="item-navigazione">CHI SIAMO <i class="far fa-question-circle"></i></a>
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
            <a href="#" class="item-navigazione">CHI SIAMO <i class="far fa-question-circle"></i></a>
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
    <p>
        Siamo nati nel 2013, e da allora operiamo nel settore dell’economia circolare dei prodotti hi-tech con passione e competenza, avendo servito complessivamente oltre 150.000 clienti e ricevuto oltre 10.700 recensioni certificate con un indice di soddisfazione della clientela pari al 92%. Siamo stati inoltre i primi ad introdurre il concetto di iPhone Ricondizionato in Italia e i primi nel nostro settore ad essere quotati in Borsa, nell'ottobre 2020. Commercializziamo i nostri Smartphone Ricondizionati in Italia attraverso il nostro sito e-commerce 2Chance.tel e una catena in espansione di 5 negozi: a Milano, 2 a Roma, Bologna e Salerno.        <br><br>
        <br>Il cuore della nostra azienda batte sia a Milano, dove abbiamo la sede legale e operativa, che nella provincia di Salerno, dove sono presenti il laboratorio di refurbishment, il magazzino ed il customer care.
        E' proprio nella provincia di Salerno, che ogni giorno i nostri tecnici si prendono cura dei vostri smartphone, riportandoli al perfetto funzionamento, pronti per iniziare una seconda vita.
        Ogni iPhone attraversa un'accurato processo di ricondizionamento in 5 fasi che inizia dai test hardware e software e finisce con la completa igienizzazione prima dell'inscatolamento. Secondo necessità, i device passano poi al reparto riparazioni dove vengono sostituite tutte le componenti usurate o non più funzionanti.<br><br>
        E' la cura dei dettagli e un cospicuo numero di test (ben 37!) che rendono gli iPhone Ricondizionati in Italia da 2Chance affidabili, sicuri e garantiti 12 mesi. 2Chance significa Ricondizionato con passione in Italia!
        Nei nostri negozi di Milano, Roma, Bologna e Salerno puoi trovare una vasta gamma di iPhone Ricondizionati, iPad Ricondizionati, Mac Ricondizionati.
        I nostri ragazzi potranno assisterti nella scelta dello smartphone ideale per le tue esigenze e potranno illustrarti la gamma di servizi che puoi abbinare al tuo smartphone ricondizionato. Ad esempio l'assicurazione contro furto e danni, la nostra library di corsi online dedicati al mondo iPhone e Mac e molto altro.
        Nei nostri negozi puoi anche vendere il tuo iPhone usato oppure permutarlo, ottenendo così uno sconto immediato sul prezzo di acquisto di un nuovo smartphone ricondizionato.

    </p>
</div>
<!-- FINE CORPO PAGINA-->
<footer class="footer">
    <p>2Chance P.IVA: 12345577777777</p>
</footer>

<style>
    #corpo-pagina p{
        width: 80vw;
        font-size: 14px;
        font-family: LemonMilk;
    }

    @media only screen and (max-width: 700px) {
        #corpo-pagina{
            flex-direction: column;
            justify-content: flex-start;
        }

        #corpo-pagina p{
            margin-top: 15px;
            font-size: 12px;
        }
    }
</style>

<script src="https://ajax.googleapis.com/ajax/libs/jquery/3.6.0/jquery.min.js"></script>
<script src="functions/index.js"></script>
<script src="functions/general.js"></script>
</body>
</html>