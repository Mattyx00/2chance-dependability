function show(){
    let obj = document.getElementById('passwordInput');
    obj.type = "text";
}

function hide(){
    let obj = document.getElementById('passwordInput');
    obj.type = "password";
}

function validateEmail(email) {
    const re = /^[\w-\.]+@([\w-]+\.)+[\w-]{2,4}$/;
    return re.test(String(email).toLowerCase());
}

function validateTesto(elemento){
    const re = /^[a-zA-Z]*$/;
    return re.test(String(elemento));
}

function validateTelefono(tel){
    const re = /^\d{10}$/;
    return re.test(String(tel));
}

function validatePassword(psw){
    const re = /^(?=.*[A-Z]).{8,}$/;
    return re.test(String(psw));
}

function controllaCampi(){
    let email = document.forms["registrazione"]["email"].value;
    let nome = document.forms["registrazione"]["nome"].value;
    let cognome = document.forms["registrazione"]["cognome"].value;
    let tel = document.forms["registrazione"]["telefono"].value;
    let psw = document.forms["registrazione"]["password"].value;
    if(!validateEmail(email)){
        alert("Inserire correttamente l'email");
        return false;
    }
    if(!validateTesto(nome)){
        alert("Inserire correttamente il nome");
        return false;
    }
    if(!validateTesto(cognome)){
        alert("Inserire correttamente il cognome");
        return false;
    }
    if(!validateTelefono(tel)){
        alert("Inserire correttamente il numero di telefono");
        return false;
    }
    if(!validatePassword(psw)){
        alert("Inserire correttamente la password (minimo 8 caratteri ed una maiuscola)");
        return false;
    }
    return true;
}