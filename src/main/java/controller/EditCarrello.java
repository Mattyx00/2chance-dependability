package controller;

import model.beans.Carrello;
import model.beans.Prodotto;
import model.beans.ProdottoCarrello;
import model.dao.ProdottoDAO;

import javax.servlet.*;
import javax.servlet.http.*;
import javax.servlet.annotation.*;
import java.io.IOException;
import java.sql.SQLException;

@WebServlet(name = "EditCarrello", value = "/EditCarrello")
public class EditCarrello extends HttpServlet {
    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        HttpSession session = request.getSession();
        Carrello carrello = (Carrello)session.getAttribute("carrello");
        Prodotto prodotto_provv = new Prodotto();

        try {
            ProdottoDAO prodottoDAO = new ProdottoDAO();
            int id_prodotto = Integer.parseInt(request.getParameter("prodotto"));
            prodotto_provv = prodottoDAO.getProdottoById(id_prodotto);
        } catch (SQLException throwables) {
            throwables.printStackTrace();
        }

        if(request.getParameter("tipo").equals("elimina")) {
            carrello.eliminaProdotto(prodotto_provv);
        }else if(request.getParameter("tipo").equals("cambiaquantita")){
            int qnt = Integer.parseInt(request.getParameter("quantita"));
            carrello.cambiaQuantita(prodotto_provv, qnt);
        }
    }

    @Override
    protected void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        doGet(request, response);
    }
}
