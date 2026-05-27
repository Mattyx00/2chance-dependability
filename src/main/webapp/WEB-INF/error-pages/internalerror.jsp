<%@ page contentType="text/html;charset=UTF-8" language="java" %>
<html>
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
    <title>ERROR 500</title>

	<link rel="shortcut icon" href="${assetHost}favicon.ico" crossorigin="anonymous">

	<link rel="stylesheet" type="text/css" media="print" href="${assetHost}css/print.css" crossorigin="anonymous">
</head>
<body>
<p>ERROR 500 - INTERNAL ERROR</p>
<style>
    *{
        margin: 0;
        padding: 0;
        background-color: #F08354;
    }

    p{
        position: absolute;
        top: 50%;
        left: 50%;
        transform: translate(-50%, -50%);
        color: white;
        font-size: 4vw;
        font-family: LemonMilk;
    }
</style>
</body>
</html>
