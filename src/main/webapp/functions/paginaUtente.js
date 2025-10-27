$(".fa-pen-square").click(function (e){
    elemento = e.target.id;
    let edit;
    if(elemento=="editImmagine"){
        $("#modificaImmagineInput").trigger('click');
        return;
    }else{
        if(elemento=="editNome"){
            edit = prompt("Inserisci il nome: ");
            if(edit==null) return false;
            if(!validateTesto(edit)){
                alert("Inserire correttamente il nome");
                return false;
            }
        }else{
            if(elemento=="editCognome"){
                edit = prompt("Inserisci il cognome: ");
                if(edit==null) return false;
                if(!validateTesto(edit)){
                    alert("Inserire correttamente il cognome");
                    return false;
                }
            }else{
                if(elemento=="editEmail"){
                    edit = prompt("Inserisci l'email: ");
                    editUrl = 'editImmagine';
                    if(edit==null) return false;
                    if(!validateEmail(edit)){
                        alert("Inserire correttamente l'email");
                        return false;
                    }
                }else{
                    if(elemento=="editTelefono"){
                        edit = prompt("Inserisci il telefono: ");
                        editUrl = 'editImmagine';
                        if(edit==null) return false;
                        if(!validateTelefono(edit)){
                            alert("Inserire correttamente il numero di telefono");
                            return false;
                        }
                    }else{
                        return false;
                    }
                }
            }
        }
    }

    //EditProfiloServlet/editImmagine <input type="file" name = "modifica"><input type="submit"></form></p>
    console.log("2chance");
    window.location.replace("EditProfiloServlet/"+elemento+"?modifica="+edit);

})

$('#modificaImmagineInput').change(function() {
    $('#formEditImmagine').submit();
});