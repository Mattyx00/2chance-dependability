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

document.querySelectorAll('.fa-pen-square').forEach(function(item) {
    item.addEventListener('click', function(e) {
        let elemento = e.target.id;
        let edit;
        if (elemento === "editImmagine") {
            const input = document.getElementById('modificaImmagineInput');
            if (input) input.click();
            return;
        } else {
            if (elemento === "editNome") {
                edit = prompt("Inserisci il nome: ");
                if (edit == null) return false;
                if (!validateTesto(edit)) {
                    alert("Inserire correttamente il nome");
                    return false;
                }
            } else if (elemento === "editCognome") {
                edit = prompt("Inserisci il cognome: ");
                if (edit == null) return false;
                if (!validateTesto(edit)) {
                    alert("Inserire correttamente il cognome");
                    return false;
                }
            } else if (elemento === "editEmail") {
                edit = prompt("Inserisci l'email: ");
                if (edit == null) return false;
                if (!validateEmail(edit)) {
                    alert("Inserire correttamente l'email");
                    return false;
                }
            } else if (elemento === "editTelefono") {
                edit = prompt("Inserisci il telefono: ");
                if (edit == null) return false;
                if (!validateTelefono(edit)) {
                    alert("Inserire correttamente il numero di telefono");
                    return false;
                }
            } else {
                return false;
            }
        }

        window.location.replace("EditProfiloServlet/" + elemento + "?modifica=" + edit);
    });
});

const fileInput = document.getElementById('modificaImmagineInput');
if (fileInput) {
    fileInput.addEventListener('change', function() {
        const form = document.getElementById('formEditImmagine');
        if (form) {
            form.submit();
        }
    });
}