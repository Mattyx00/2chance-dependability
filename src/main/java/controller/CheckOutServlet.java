package controller;

import model.beans.Carrello;
import model.beans.Ordine;
import model.beans.ProdottoCarrello;
import model.beans.Utente;
import model.dao.OrdineDAO;

import javax.servlet.*;
import javax.servlet.http.*;
import javax.servlet.annotation.*;
import java.io.IOException;
import java.sql.SQLException;
import java.util.ArrayList;

@WebServlet(name = "CheckOutServlet", value = "/CheckOutServlet")
public class CheckOutServlet extends HttpServlet {
    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {

        if(request.getSession().getAttribute("user") == null){
            response.sendRedirect( request.getServletContext().getContextPath()+"/login.jsp");
            return;
        }

        Carrello carrello =  (Carrello)(request.getSession().getAttribute("carrello")); //prendo il carrello dalla sessione
        ArrayList<ProdottoCarrello> prodotti =  carrello.getProdotti();
        try {
            OrdineDAO dao = new OrdineDAO();
            Ordine ordine = new Ordine();

                double totale = carrello.getTotaleCarrello();
                String indirizzo = request.getParameter("indirizzo");
                Utente utente = (Utente)(request.getSession().getAttribute("user"));

                ordine.setUtente(utente);
                ordine.setIndirizzo(indirizzo);
                ordine.setPrezzoTotale(totale);
                ordine.setCarrello(carrello);

               dao.addOrdine(ordine);



            HttpSession session = request.getSession();
            session.removeAttribute("carrello");
            OrdineDAO ordineprovv = new OrdineDAO();
            ArrayList<Ordine> ordini = ordineprovv.getOrdiniByUtente(utente);
            utente.setOrdini(ordini);
            session.setAttribute("user", utente);
            response.sendRedirect( request.getServletContext().getContextPath()+"/landingpage");


        } catch (SQLException throwables) {
            throwables.printStackTrace();
        }


    }

    @Override
    protected void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        doGet(request, response);
    }
}
