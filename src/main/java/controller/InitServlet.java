package controller;

import model.beans.Categoria;
import model.beans.Prodotto;
import model.dao.CategoriaDAO;
import model.dao.ProdottoDAO;

import javax.servlet.*;
import javax.servlet.http.*;
import javax.servlet.annotation.*;
import java.io.IOException;
import java.sql.SQLException;
import java.util.ArrayList;

@WebServlet(name = "InitServlet", value = "/InitServlet", loadOnStartup = 0)
public class InitServlet extends HttpServlet {

    @Override
    public void init() throws ServletException {
        super.init();
        try {
            CategoriaDAO dao = new CategoriaDAO();
            ArrayList<Categoria> categorie = dao.getCategorie();

            getServletContext().setAttribute("categorie", categorie);

            ProdottoDAO pDao = new ProdottoDAO();
            ArrayList<Prodotto> prodotti = pDao.getUltimiProdotti();
            getServletContext().setAttribute("prodotti", prodotti);


        } catch (SQLException e) {
            e.printStackTrace();
        }
    }

}
