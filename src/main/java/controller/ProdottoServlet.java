package controller;

import model.beans.Prodotto;
import model.dao.ProdottoDAO;

import javax.servlet.*;
import javax.servlet.http.*;
import javax.servlet.annotation.*;
import java.io.IOException;
import java.sql.SQLException;
import java.util.ArrayList;

@WebServlet(name = "ProdottoServlet", value = "/ProdottoServlet")
public class ProdottoServlet extends HttpServlet {
    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        try {
            ProdottoDAO dao = new ProdottoDAO();
            Prodotto prod = dao.getProdottoById(Integer.parseInt(request.getParameter("prodotto")));
            request.setAttribute("prodotto", prod);
            /* for(int i=0; i<prod.getRecensioni().size(); i++){
                System.out.println(prod.getRecensioni().get(i).getTesto());
                System.out.println(prod.getRecensioni().get(i).getUtente().getNome());
            } */

            String address = "/paginaProdotto.jsp";
            RequestDispatcher dispatcher = request.getRequestDispatcher(address);
            dispatcher.forward(request, response);

        } catch (SQLException throwables) {
            throwables.printStackTrace();
        }

    }

    @Override
    protected void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        doGet(request, response);
    }
}
